extern crate clap;
extern crate regex;
extern crate serde;
#[macro_use]
extern crate serde_derive;
extern crate serde_json;

mod structs;

use std::fs;
use std::io::{Read, Write};
use std::process;

use std::collections::BTreeMap;

#[cfg_attr(rustfmt, rustfmt_skip)]
static HEADER_H : &'static str = "\
//===-- InstBuilder.h - SPIR-V instruction builder --------------*- C++ -*-===//\n";

#[cfg_attr(rustfmt, rustfmt_skip)]
static HEADER_CPP : &'static str = "\
//===-- InstBuilder.cpp - SPIR-V instruction builder ------------*- C++ -*-===//\n";

#[cfg_attr(rustfmt, rustfmt_skip)]
static COPYRIGHT : &'static str = "\
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//";

#[cfg_attr(rustfmt, rustfmt_skip)]
static AUTOGEN_COMMENT : &'static str = "\
// AUTOMATICALLY GENERATED from the SPIR-V JSON grammar:
//   spirv.core.grammar.json.
// DO NOT MODIFY!";

pub fn write_copyright_autogen_comment(file: &mut fs::File, header: &str) {
    file.write_all(header.as_bytes()).unwrap();
    file.write_all(COPYRIGHT.as_bytes()).unwrap();
    file.write_all(b"\n\n").unwrap();
    file.write_all(AUTOGEN_COMMENT.as_bytes()).unwrap();
    file.write_all(b"\n\n").unwrap();
}

macro_rules! write {
    ($content: expr, $path: expr, $header: expr) => {
        {
            let mut f = fs::File::create($path).expect(&format!("cannot open file: {}", $path));
            write_copyright_autogen_comment(&mut f, $header);
            f.write_all(&$content.into_bytes()).unwrap();
            let mut cmd = process::Command::new("clang-format")
                .arg("-i").arg("-style=LLVM").arg($path)
                .spawn().expect("failed to execute clang-format");
            let ec = cmd.wait().expect("failed to wait on clang-format");
            assert!(ec.success());
        }
    }
}

/// Converts the given `symbol` to use snake case style.
pub fn snake_casify(symbol: &str) -> String {
    let re = regex::Regex::new(r"(?P<l>[a-z])(?P<u>[A-Z])").unwrap();
    re.replace_all(symbol, "$l-$u").replace("-", "_").to_lowercase()
}

fn get_cpp_type(kind: &str, category: &str) -> String {
    if kind.starts_with("Id") || kind == "LiteralInteger" || kind == "LiteralExtInstInteger" {
        "uint32_t".to_string()
    } else if kind == "LiteralSpecConstantOpInteger" {
        "spv::Op".to_string()
    } else if kind == "LiteralContextDependentNumber" {
        panic!("this kind is not expected to be handled here")
    } else if kind == "LiteralString" {
        "std::string".to_string()
    } else if kind.starts_with("Pair") {
        "std::pair<uint32_t, uint32_t>".to_string()
    } else if category == "BitEnum" {
        format!("spv::{}Mask", kind)
    } else {
        format!("spv::{}", kind)
    }
}

/// Returns a suitable name for the given parameter.
fn get_param_name(param: &structs::Operand) -> String {
    if param.name.len() == 0 {
        if param.kind == "IdResultType" {
            "result_type".to_string()
        } else if param.kind == "IdResult" {
            "result_id".to_string()
        } else {
            snake_casify(&param.kind)
        }
    } else {
        if param.name == "'Default'" {
            "default_target".to_string()
        } else {
            let re = regex::Regex::new(r"\W").unwrap();
            snake_casify(&re.replace_all(&param.name.replace(" ", "_"), ""))
        }
    }
}

/// Returns the parameter list.
fn get_param_list(params: &[structs::Operand], kinds: &[structs::OperandKind]) -> String {
    let list: Vec<String> = params.iter()
        .map(|param| {
            let name = get_param_name(param);
            let kind = get_cpp_type(&param.kind, &get_category(param, kinds));
            if param.quantifier == "" {
                format!("{} {}", kind, name)
            } else if param.quantifier == "?" {
                format!("llvm::Optional<{}> {}", kind, name)
            } else {
                format!("llvm::ArrayRef<{}> {}", kind, name)
            }
        })
        .collect();
    list.join(", ")
}

/// Returns a suitable function name for the given `symbol`.
fn get_function_name(symbol: &str) -> String {
    let mut chars = symbol.chars();
    match chars.next() {
        None => String::new(),
        Some(c) => c.to_lowercase().collect::<String>() + chars.as_str(),
    }
}

fn get_encode_inst_signature(inst: &structs::Instruction,
                             kinds: &[structs::OperandKind],
                             full_qualified: bool)
                             -> String {
    format!("InstBuilder& {}{}({})",
            if full_qualified { "InstBuilder::" } else { "" },
            get_function_name(&inst.opname),
            get_param_list(&inst.operands, kinds))
}

fn get_encode_operand_signature(kind: &structs::OperandKind, full_qualified: bool) -> String {
    format!("void {qual}encode{kind}(spv::{kind}{mask} value)",
            qual = if full_qualified { "InstBuilder::" } else { "" },
            kind = kind.kind,
            mask = if kind.category == "BitEnum" {
                "Mask"
            } else {
                ""
            })
}

fn get_fixup_operand_signature(candidates: &[String],
                               kinds: &[structs::OperandKind])
                               -> Vec<String> {
    kinds.iter()
        .filter(|kind| candidates.iter().find(|c| **c == kind.kind).is_some())
        .map(|kind| {
                 format!("InstBuilder& {name}({ty})",
                         name = get_function_name(&kind.kind),
                         ty = get_cpp_type(&kind.kind, &kind.category))
             })
        .collect()
}

fn encode_param(name: &str, kind: &str, context: &Context) -> String {
    let category = &context.get_operand_kind(kind).category;
    if category == "Id" {
        format!("TheInst.emplace_back({});", name)
    } else if category == "Literal" {
        if kind == "LiteralString" {
            format!("encodeString({});", name)
        } else if kind == "LiteralContextDependentNumber" {
            panic!("this kind is not expected to be handled here")
        } else if kind == "LiteralSpecConstantOpInteger" {
            format!("TheInst.emplace_back(static_cast<uint32_t>({}));", name)
        } else {
            format!("TheInst.emplace_back({});", name)
        }
    } else if category == "Composite" {
        format!("TheInst.emplace_back({name}.first); TheInst.emplace_back({name}.second);",
                name = name)
    } else if context.has_additional_params(kind) {
        format!("encode{}({});", kind, name)
    } else {
        assert!(category == "BitEnum" || category == "ValueEnum");
        format!("TheInst.emplace_back(static_cast<uint32_t>({}));", name)
    }
}

fn get_fixup_operand_impl(candidates: &[String], context: &Context) -> Vec<String> {
    context.grammar
        .operand_kinds
        .iter()
        .filter(|kind| candidates.iter().find(|c| **c == kind.kind).is_some())
        .map(|kind| {
            let encode = encode_param("value", &kind.kind, context);
            format!("InstBuilder& InstBuilder::{name}({ty} value) {{
                       if (Expectation.front() != OperandKind::{kind}) {{
                         TheStatus = Status::Expect{kind};
                         return *this;
                       }}
                       Expectation.pop_front();
                       {encode}
                       return *this;
                     }}",
                    kind = kind.kind,
                    name = get_function_name(&kind.kind),
                    encode = encode,
                    ty = get_cpp_type(&kind.kind, &kind.category))
        })
        .collect()
}

fn gen_inst_builder_h(context: &Context) -> String {
    let grammar = context.grammar;
    let inst_methods: Vec<String> = grammar.instructions
        .iter()
        .filter(|inst| inst.opname != "OpConstant" && inst.opname != "OpSpecConstant")
        .map(|inst| get_encode_inst_signature(inst, &grammar.operand_kinds, false))
        .collect();
    let operand_methods: Vec<String> = grammar.operand_kinds
        .iter()
        .filter(|kind| context.has_additional_params(&kind.kind))
        .map(|kind| get_encode_operand_signature(kind, false))
        .collect();
    let param_kinds = get_additional_param_kinds(&grammar.operand_kinds);
    let fixup_methods = get_fixup_operand_signature(&param_kinds, &grammar.operand_kinds);
    let mut index = 4;
    let error_codes: Vec<String> = param_kinds.iter()
        .map(|kind| {
                 index += 1;
                 format!("Expect{} = -{}", kind, index)
             })
        .collect();
    format!("#ifndef LLVM_CLANG_SPIRV_INSTBUILDER_H
             #define LLVM_CLANG_SPIRV_INSTBUILDER_H

             #include <deque>
             #include <functional>
             #include <string>
             #include <utility>
             #include <vector>

             #include \"spirv/1.0/spirv.hpp11\"
             #include \"llvm/ADT/ArrayRef.h\"
             #include \"llvm/ADT/Optional.h\"

             namespace clang {{
             namespace spirv {{

             /// \\brief SPIR-V word consumer.
             using WordConsumer = std::function<void(std::vector<uint32_t> &&)>;

/// \\brief A low-level SPIR-V instruction builder that generates SPIR-V words
/// directly. All generated SPIR-V words will be fed into the WordConsumer
/// passed in the constructor.
///
/// The methods of this builder reflects the layouts of the corresponding
/// SPIR-V instructions. For example, to construct an \"OpMemoryModel Logical
/// Simple\" instruction, just call InstBuilder::opMemoryModel(
/// spv::AddressingModel::Logical, spv::MemoryModel::Simple).
///
/// For SPIR-V instructions that may take additional parameters depending on
/// the value of some previous parameters, additional methods are provided to
/// \"fix up\" the instruction under building. For example, to construct an
/// \"OpDecorate <target-id> ArrayStride 0\" instruction, just call InstBuilder::
/// opDecorate(<target-id>, spv::Decoration::ArrayStride).literalInteger(0).
///
/// .x() is required to finalize the building and feed the result to the
/// consumer. On failure, if additional parameters are needed, the first missing
/// one will be reported by .x() via InstBuilder::Status.
             class InstBuilder {{
             public:
             /// Status of instruction building.
             enum class Status: int32_t {{
               Success = 0,
               NullConsumer = -1,
               NestedInst = -2,
               ZeroResultType = -3,
               ZeroResultId = -4,
               {error_codes}
             }};

             explicit InstBuilder(WordConsumer);

             // Disable copy constructor/assignment.
             InstBuilder(const InstBuilder &) = delete;
             InstBuilder &operator=(const InstBuilder &) = delete;

             // Allow move constructor/assignment.
             InstBuilder(InstBuilder &&that) = default;
             InstBuilder &operator=(InstBuilder &&that) = default;

             void setConsumer(WordConsumer);
             const WordConsumer &getConsumer() const;

             /// \\brief Finalizes the building and feeds the generated SPIR-V words
             /// to the consumer.
             Status x();
             /// \\brief Finalizes the building and returns the generated SPIR-V words.
             /// Returns an empty vector if errors happened during the construction.
             std::vector<uint32_t> take();

             /// \\brief Clears the current instruction under building.
             void clear();

             // Instruction building methods.
             {inst_methods};

             // All-in-one method for creating binary operations.
             InstBuilder &binaryOp(spv::Op op, uint32_t result_type, uint32_t result_id,
                                   uint32_t lhs, uint32_t rhs);

             // Methods for building constants.
             InstBuilder &opConstant(uint32_t result_type, uint32_t result_id,
                                     uint32_t value);

             // Methods for supplying additional parameters.
             {fixup_methods};

             private:
               enum class OperandKind {{
                 {kinds}
               }};

               {operand_methods};
               void encodeString(std::string value);

               WordConsumer TheConsumer;
               std::vector<uint32_t> TheInst; ///< The instruction under construction.
               std::deque<OperandKind> Expectation; ///< Expected additional parameters.
               Status TheStatus; ///< Current building status.
             }};

             }} // end namespace spirv
             }} // end namespace clang

             #endif\n",
            kinds = param_kinds.join(",\n"),
            error_codes = error_codes.join(",\n"),
            inst_methods = inst_methods.join(";\n"),
            fixup_methods = fixup_methods.join(";\n"),
            operand_methods = operand_methods.join(";\n"))
}

fn check_opcode_result_type_id(inst: &structs::Instruction) -> String {
    let mut result = "if (!TheInst.empty()) { TheStatus = Status::NestedInst; return *this; }\n"
        .to_string();
    if !inst.operands.is_empty() {
        let mut index = 0;
        if inst.operands[index].kind == "IdResultType" {
            result += "if (result_type == 0) \
                       { TheStatus = Status::ZeroResultType; return *this; }\n";
            index += 1;
        }
        if inst.operands[index].kind == "IdResult" {
            result += "if (result_id == 0) { TheStatus = Status::ZeroResultId; return *this; }\n";
        }
    }
    result
}

fn push_argument(name: &str, kind: &str, quantifier: &str, context: &Context) -> String {
    if quantifier == "" {
        encode_param(name, kind, context)
    } else if quantifier == "?" {
        format!("if ({name}.hasValue()) {{ const auto& val = {name}.getValue(); {sub} }}",
                name = name,
                sub = push_argument("val", kind, "", context))
    } else {
        if kind.starts_with("Id") {
            format!("TheInst.insert(TheInst.end(), {name}.begin(), {name}.end());",
                    name = name)
        } else {
            format!("for (const auto& param : {name}) {{ {sub}; }}",
                    name = name,
                    sub = push_argument("param", kind, "", context))
        }
    }
}

fn get_category(param: &structs::Operand, kinds: &[structs::OperandKind]) -> String {
    kinds.iter()
        .find(|x| x.kind == param.kind)
        .expect("should found")
        .category
        .to_string()
}

fn push_arguments(params: &[structs::Operand], context: &Context) -> String {
    if params.is_empty() {
        return String::new();
    }
    let list: Vec<String> = params.iter()
        .map(|param| {
                 push_argument(&get_param_name(&param),
                               &param.kind,
                               &param.quantifier,
                               context)
             })
        .collect();
    list.join("\n")
}

fn get_build_inst_impl(inst: &structs::Instruction, context: &Context) -> String {
    format!("{signature} {{
               {result_type_id}
               TheInst.reserve({count});
               TheInst.emplace_back(static_cast<uint32_t>(spv::Op::{opname}));
               {operands}

               return *this;
             }}",
            signature = get_encode_inst_signature(inst, &context.grammar.operand_kinds, true),
            count = inst.operands.len() + 1,
            opname = inst.opname,
            result_type_id = check_opcode_result_type_id(inst),
            operands = push_arguments(&inst.operands, context))
}

fn get_build_operand_impl(kind: &structs::OperandKind) -> Option<String> {
    if kind.category == "ValueEnum" {
        let cases: Vec<String> = kind.enumerants
            .iter()
            .filter_map(|e| if e.parameters.len() == 0 {
                None
            } else {
                let params: Vec<String> = e.parameters
                    .iter()
                    .map(|p| format!("Expectation.emplace_back(OperandKind::{})", p.kind))
                    .collect();
                Some(format!("  case spv::{kind}::{symbol}: {{ {expect}; }} break;",
                             kind = kind.kind,
                             symbol = e.symbol,
                             expect = params.join("; ")))
            })
            .collect();
        if cases.len() == 0 {
            // No enumerant need additional arguments, therefore no need for
            // special encoding method for this operand kind.
            None
        } else {
            Some(format!("{signature} {{
                            switch (value) {{
                              {cases}
                              default: break;
                          }}

                          TheInst.emplace_back(static_cast<uint32_t>(value));
                          }}",
                         signature = get_encode_operand_signature(kind, true),
                         cases = cases.join("\n")))
        }
    } else if kind.category == "BitEnum" {
        let cases: Vec<String> = kind.enumerants
            .iter()
            .filter_map(|e| if e.parameters.len() == 0 {
                None
            } else {
                let params: Vec<String> = e.parameters
                    .iter()
                    .map(|p| format!("Expectation.emplace_back(OperandKind::{})", p.kind))
                    .collect();
                Some(format!("if (bitEnumContains(value, spv::{kind}Mask::{symbol})) \
                              {{ {expect}; }}",
                             kind = kind.kind,
                             symbol = e.symbol,
                             expect = params.join("; ")))
            })
            .collect();
        if cases.len() == 0 {
            // No enumerant need additional arguments, therefore no need for
            // special encoding method for this operand kind.
            None
        } else {
            Some(format!("{signature} {{
                            {cases}
                            TheInst.emplace_back(static_cast<uint32_t>(value));
                          }}",
                         signature = get_encode_operand_signature(kind, true),
                         cases = cases.join("\n")))
        }
    } else {
        panic!("only ValueEnum and BitEnum are handled here");
    }
}

/// Returns all operand kinds used in additional parameters for BitEnum and
/// ValueEnum enumerants.
fn get_additional_param_kinds(kinds: &[structs::OperandKind]) -> Vec<String> {
    let mut result: Vec<String> = kinds.iter()
        .flat_map(|k| {
                      k.enumerants.iter().flat_map(|e| e.parameters.iter().map(|p| p.kind.clone()))
                  })
        .collect();
    result.sort();
    result.dedup();
    result
}

/// Returns a list of bitEnumContains() functions for all BitEnums that can
/// potentially require additional parameters.
fn get_contain_function(kind: &structs::OperandKind, context: &Context) -> Option<String> {
    if kind.category == "BitEnum" && context.has_additional_params(&kind.kind) {
        Some(format!("inline bool bitEnumContains(spv::{kind}Mask bits, spv::{kind}Mask bit) {{ \
                      return (uint32_t(bits) & uint32_t(bit)) != 0; }}",
                     kind = kind.kind))
    } else {
        None
    }
}

fn gen_inst_builder_cpp(context: &Context) -> String {
    let grammar = context.grammar;
    let inst_impls: Vec<String> = grammar.instructions
        .iter()
        .filter(|inst| inst.opname != "OpConstant" && inst.opname != "OpSpecConstant")
        .map(|inst| get_build_inst_impl(inst, context))
        .collect();
    let operand_impls: Vec<String> = grammar.operand_kinds
        .iter()
        .filter(|kind| kind.category == "ValueEnum" || kind.category == "BitEnum")
        .filter_map(|kind| get_build_operand_impl(kind))
        .collect();
    let contain_impls: Vec<String> = grammar.operand_kinds
        .iter()
        .filter(|kind| kind.category == "BitEnum")
        .filter_map(|kind| get_contain_function(kind, context))
        .collect();
    let param_kinds = get_additional_param_kinds(&grammar.operand_kinds);
    let fixup_impls = get_fixup_operand_impl(&param_kinds, context);
    let errors: Vec<String> = param_kinds.iter()
        .map(|kind| format!("case OperandKind::{k}: return Status::Expect{k};", k = kind))
        .collect();
    format!("#include \"clang/SPIRV/InstBuilder.h\"

             namespace clang {{
             namespace spirv {{

             static_assert(spv::Version == {version:#010x} && spv::Revision == {revision},
                           \"Needs to regenerate outdated InstBuilder\");

             namespace {{
             {contains}
             }}

             InstBuilder::InstBuilder(WordConsumer consumer)
               : TheConsumer(consumer), TheStatus(Status::Success) {{}}

             void InstBuilder::setConsumer(WordConsumer consumer) {{ TheConsumer = consumer; }}
             const WordConsumer &InstBuilder::getConsumer() const {{ return TheConsumer; }}

             InstBuilder::Status
             InstBuilder::x() {{
               if (TheConsumer == nullptr) return Status::NullConsumer;

               if (TheStatus != Status::Success) return TheStatus;

               if (!Expectation.empty()) {{
                 switch (Expectation.front()) {{
                   {errors}
                 }}
               }}

               if (!TheInst.empty()) TheInst.front() |= uint32_t(TheInst.size()) << 16;
               TheConsumer(std::move(TheInst));
               TheInst.clear();

               return TheStatus;
             }}

             void InstBuilder::clear() {{
               TheInst.clear();
               Expectation.clear();
               TheStatus = Status::Success;
             }}

             {inst_methods}

             {operand_methods}

             {fixup_methods}

             }} // end namespace spirv
             }} // end namespace clang\n",
            errors = errors.join("\n"),
            contains = contain_impls.join("\n"),
            inst_methods = inst_impls.join("\n\n"),
            fixup_methods = fixup_impls.join("\n\n"),
            operand_methods = operand_impls.join("\n\n"),
            version = (grammar.major_version << 16) | grammar.minor_version,
            revision = grammar.revision)
}

struct Context<'a> {
    /// The SPIR-V grammar
    grammar: &'a structs::Grammar,
    /// Mapping from SPIR-V operand kind names to their grammar
    operand_kinds: BTreeMap<&'a str, &'a structs::OperandKind>,
    /// Mapping from SIPR-V operand kind names to whether may have additional parameters
    with_additional_params: BTreeMap<&'a str, bool>,
}

impl<'a> Context<'a> {
    pub fn new(grammar: &'a structs::Grammar) -> Context<'a> {
        let mut ret = Context {
            grammar: grammar,
            operand_kinds: BTreeMap::new(),
            with_additional_params: BTreeMap::new(),
        };

        for kind in &grammar.operand_kinds {
            let key = &kind.kind;
            ret.operand_kinds.insert(key, kind);
            let has_param = kind.enumerants.iter().any(|e| !e.parameters.is_empty());
            ret.with_additional_params.insert(key, has_param);
        }

        ret
    }

    /// Returns the grammar for the given operand kind.
    pub fn get_operand_kind(&self, kind: &str) -> &'a structs::OperandKind {
        *self.operand_kinds.get(&kind).expect("key not found")
    }

    /// Returns whether the operand kind may have additional parameters.
    pub fn has_additional_params(&self, kind: &str) -> bool {
        *self.with_additional_params.get(&kind).expect("key not found")
    }
}

fn main() {
    let matches = clap::App::new("SPIR-V builder generator")
        .arg(clap::Arg::with_name("grammar")
                 .help("SPIR-V core grammar file")
                 .required(true)
                 .index(1))
        .get_matches();
    let input = matches.value_of("grammar").unwrap();

    let mut contents = String::new();
    {
        let mut file = fs::File::open(input).unwrap();
        file.read_to_string(&mut contents).unwrap();
    }
    let grammar: structs::Grammar = serde_json::from_str(&contents).unwrap();

    let context = Context::new(&grammar);

    write!(gen_inst_builder_h(&context), "InstBuilder.h", HEADER_H);
    write!(gen_inst_builder_cpp(&context),
           "InstBuilderAuto.cpp",
           HEADER_CPP);
}
