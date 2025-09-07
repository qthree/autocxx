// Copyright 2020 Google LLC
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// https://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or https://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

use indexmap::IndexSet;

use syn::{parse_quote, punctuated::Punctuated, token::Comma, Field, Visibility};

use crate::{
    conversion::{
        api::{
            Api, ApiName, FuncToConvert, Provenance, StructDetails, TypeKind,
        },
        apivec::ApiVec,
        error_reporter::convert_apis, type_helpers::type_is_reference,
    },
    known_types,
    minisyn::FnArg,
    types::{make_ident, QualifiedName},
};

use super::{
    fun::function_wrapper::{CppFunctionBody, CppFunctionKind},
    pod::{PodAnalysis, PodPhase},
};

struct StructAccessGenerator {
    existing_api: IndexSet<QualifiedName>,
    pod_safe_types: IndexSet<QualifiedName>,
    accessors: ApiVec<PodPhase>,
}

#[derive(Clone, Copy)]
enum AccessType {
    Get,
    Set
}

impl StructAccessGenerator {
    fn take_accessors(&mut self) -> ApiVec<PodPhase> {
        std::mem::take(&mut self.accessors)
    }
    fn generate(&mut self, struct_name: &ApiName, field: &Field, access_type: AccessType) {
        let field_name = field.ident.as_ref().unwrap().to_string();
        let accessor_name = get_accessor_name(&struct_name.name, &field_name, access_type);
        let ident = accessor_name.get_final_ident();

        if !should_generate_accessor(
            field,
            &self.existing_api,
            &accessor_name,
            &self.pod_safe_types,
        ) {
            return;
        }

        let field_name_ident = make_ident(field_name);

        let body = match access_type {
            AccessType::Get => CppFunctionBody::GetField(field_name_ident),
            AccessType::Set => CppFunctionBody::SetField(field_name_ident),
        };

        let struct_type = struct_name.name.to_type_path();

        // TODO: convert arrays to pointers?
        let field_type = &field.ty;

        let inputs: Punctuated<FnArg, Comma> = match access_type {
            AccessType::Get => parse_quote! {
                this: *const #struct_type
            },
            AccessType::Set =>  parse_quote! {
                this: *mut #struct_type, value: #field_type
            },
        };

        let output = match access_type {
            AccessType::Get => parse_quote!{
                -> #field_type
            },
            AccessType::Set =>  parse_quote! {
            },
        };

        self.accessors.push(Api::Function {
            name: ApiName::new_from_qualified_name(accessor_name),
            fun: Box::new(FuncToConvert {
                provenance: Provenance::SynthesizedOther,
                ident,
                doc_attrs: Vec::new(),
                inputs,
                variadic: false,
                output,
                vis: parse_quote! { pub },
                virtualness: None,
                cpp_vis: crate::conversion::api::CppVisibility::Public,
                special_member: None,
                original_name: None,
                self_ty: None,
                synthesized_this_type: None,
                add_to_trait: None,
                synthetic_cpp: Some((body, CppFunctionKind::Function)),
                is_deleted: None,
            }),
            analysis: (),
        })
    }
}

pub(crate) fn add_field_accessors(apis: ApiVec<PodPhase>) -> ApiVec<PodPhase> {
    let mut gen = StructAccessGenerator {
        existing_api: apis.iter().map(|api| api.name().clone()).collect(),
        pod_safe_types: build_pod_safe_type_set(&apis),
        accessors: ApiVec::default(),
    };

    let mut results = ApiVec::new();
    convert_apis(
        apis,
        &mut results,
        Api::fun_unchanged,
        |struct_name: ApiName, details: Box<StructDetails>, analysis: PodAnalysis| {
            match &details.item.fields {
                syn::Fields::Named(named) => {
                    for field in named.named.iter() {
                        gen.generate(&struct_name, field, AccessType::Get);
                        gen.generate(&struct_name, field, AccessType::Set);
                    }
                }
                syn::Fields::Unnamed(_) => {}
                syn::Fields::Unit => {}
            };

            // Generate the accessors (if any) + the struct itself
            Ok(Box::new(gen.take_accessors().into_iter().chain(std::iter::once(
                Api::Struct {
                    name: struct_name,
                    details,
                    analysis,
                },
            ))))
        },
        Api::enum_unchanged,
        Api::typedef_unchanged,
    );

    results
}

fn should_generate_accessor(
    field: &Field,
    existing_api: &IndexSet<QualifiedName>,
    accessor_name: &QualifiedName,
    pod_safe_types: &IndexSet<QualifiedName>,
) -> bool {
    // Don't generate accessors that would conflict with existing api (i.e., if a method with the name we would generate already exists)
    if existing_api.contains(accessor_name) {
        return false;
    }

    // Don't generate accessors for non-public fields
    if !matches!(field.vis, Visibility::Public(_)) {
        return false;
    }

    // Don't generate accessors for cpp reference fields (this restriction may be lifted in the future)
    if type_is_reference(&field.ty, false) || type_is_reference(&field.ty, true) {
        return false;
    }

    // Don't generate accessors for "fake" bindgen fields which wouldn't appear directly in the C++ struct
    let field_name = field.ident.as_ref().unwrap().to_string();
    if field_name == "vtable_" || field_name == "_address" || field_name == "_base" {
        return false;
    }

    // Don't generate accessors for fields which are non-POD types (this restriction may be lifted in the future)
    match &field.ty {
        syn::Type::Path(path) => {
            if !pod_safe_types.contains(&QualifiedName::from_type_path(path)) {
                return false;
            }
        }
        _ => {
            return false;
        }
    }

    true
}

fn get_accessor_name(struct_name: &QualifiedName, field_name: &str, access_type: AccessType) -> QualifiedName {
    let prefix = match access_type {
        AccessType::Get => "get",
        AccessType::Set => "set",
    };
    let accessor_name = format!("{prefix}_{}", field_name);

    QualifiedName::new(struct_name.get_namespace(), make_ident(accessor_name))
}

// TODO: relocate FnAnalyzer::build_pod_safe_type_set to deduplicate
fn build_pod_safe_type_set(apis: &ApiVec<PodPhase>) -> IndexSet<QualifiedName> {
    apis.iter()
        .filter_map(|api| match api {
            Api::Struct {
                analysis:
                    PodAnalysis {
                        kind: TypeKind::Pod,
                        ..
                    },
                ..
            } => Some(api.name().clone()),
            Api::Enum { .. } => Some(api.name().clone()),
            Api::ExternCppType { pod: true, .. } => Some(api.name().clone()),
            _ => None,
        })
        .chain(
            known_types()
                .get_pod_safe_types()
                .filter_map(
                    |(tn, is_pod_safe)| {
                        if is_pod_safe {
                            Some(tn)
                        } else {
                            None
                        }
                    },
                ),
        )
        .collect()
}
