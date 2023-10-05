module DPE.Messages.Spec
module Cddl = CDDL.Spec
module Cbor = CBOR.Spec
module U64 = FStar.UInt64
module U8 = FStar.UInt8

(* TCG DICE Protection Engine, Version 1.0, Revision 0.6 *)

// Section 5.9.2: DPE uses CBOR (RFC 8949) Section 4.2.1
let data_item_order = Cbor.deterministically_encoded_cbor_map_key_order

// Section 5.9.3
let session_message = Cddl.t_array3 (
  Cddl.array_group3_item (* session-id *) Cddl.uint `Cddl.array_group3_concat`
  Cddl.array_group3_item (* message *) Cddl.bytes
)

// Section 5.9.4
let get_profile = 1uL
let open_session = 2uL
let close_session = 3uL
let sync_session = 4uL
let export_session = 5uL
let import_session = 6uL
let initialize_context = 7uL
let derive_child = 8uL
let certify_key = 9uL
let sign = 10uL
let seal = 11uL
let unseal = 12uL
let derive_sealing_public_key = 13uL
let rotate_context_handle = 14uL
let destroy_context = 15uL

let command_id =
  Cddl.t_uint_literal get_profile `Cddl.t_choice`
  Cddl.t_uint_literal open_session `Cddl.t_choice`
  Cddl.t_uint_literal close_session `Cddl.t_choice`
  Cddl.t_uint_literal sync_session `Cddl.t_choice`
  Cddl.t_uint_literal export_session `Cddl.t_choice`
  Cddl.t_uint_literal import_session `Cddl.t_choice`
  Cddl.t_uint_literal initialize_context `Cddl.t_choice`
  Cddl.t_uint_literal derive_child `Cddl.t_choice`
  Cddl.t_uint_literal certify_key `Cddl.t_choice`
  Cddl.t_uint_literal sign `Cddl.t_choice`
  Cddl.t_uint_literal seal `Cddl.t_choice`
  Cddl.t_uint_literal unseal `Cddl.t_choice`
  Cddl.t_uint_literal derive_sealing_public_key `Cddl.t_choice`
  Cddl.t_uint_literal rotate_context_handle `Cddl.t_choice`
  Cddl.t_uint_literal destroy_context

let no_error = 0uL
let internal_error = 1uL
let invalid_command = 2uL
let invalid_argument = 3uL
let argument_not_supported = 4uL
let session_exhausted = 5uL

let error_code =
  Cddl.t_uint_literal no_error `Cddl.t_choice`
  Cddl.t_uint_literal internal_error `Cddl.t_choice`
  Cddl.t_uint_literal invalid_command `Cddl.t_choice`
  Cddl.t_uint_literal invalid_argument `Cddl.t_choice`
  Cddl.t_uint_literal argument_not_supported `Cddl.t_choice`
  Cddl.t_uint_literal session_exhausted

let _input_args = ()
let _output_args = ()

// Section 7.4
let _pd_attribute_bool = ()
let _pd_attribute_number = ()
let _pd_attribute_string = ()

[@@_pd_attribute_string] let pd_name = 1uL
[@@_pd_attribute_number] let pd_dpe_spec_version = 2uL
[@@_pd_attribute_number] let pd_max_message_size = 3uL
[@@_pd_attribute_bool] let pd_uses_multi_part_messaghes = 4uL
[@@_pd_attribute_bool] let pd_supports_concurrent_operations = 5uL
[@@_pd_attribute_bool] let pd_supports_encrypted_sessions = 6uL
[@@_pd_attribute_bool] let pd_supports_derived_sessions = 7uL
[@@_pd_attribute_number] let pd_max_sessions = 8uL
[@@_pd_attribute_string] let pd_session_protocol = 9uL
[@@_pd_attribute_bool] let pd_supports_session_sync = 10uL
[@@_pd_attribute_string] let pd_session_sync_policy = 11uL
[@@_pd_attribute_bool] let pd_supports_session_migration = 12uL
[@@_pd_attribute_string] let pd_session_migration_protocol = 13uL
[@@_pd_attribute_bool] let pd_supports_default_context = 14uL
[@@_pd_attribute_bool] let pd_supports_context_handles = 15uL
[@@_pd_attribute_number] let pd_max_contexts_per_session = 16uL
[@@_pd_attribute_number] let pd_max_context_handle_size = 17uL
[@@_pd_attribute_bool] let pd_supports_auto_init = 18uL
[@@_pd_attribute_bool] let pd_supports_simulation = 19uL
[@@_pd_attribute_bool] let pd_supports_attestation = 20uL
[@@_pd_attribute_bool] let pd_supports_sealing = 21uL
[@@_pd_attribute_bool] let pd_supports_get_profile = 22uL
[@@_pd_attribute_bool] let pd_supports_open_session = 23uL
[@@_pd_attribute_bool] let pd_supports_close_session = 24uL
[@@_pd_attribute_bool] let pd_supports_sync_session = 25uL
[@@_pd_attribute_bool] let pd_supports_export_session = 26uL
[@@_pd_attribute_bool] let pd_supports_import_session = 27uL
[@@_pd_attribute_bool] let pd_supports_init_context = 28uL
[@@_pd_attribute_bool] let pd_supports_certify_key = 29uL
[@@_pd_attribute_bool] let pd_supports_sign = 30uL
[@@_pd_attribute_bool] let pd_supports_seal = 31uL
[@@_pd_attribute_bool] let pd_supports_unseal = 32uL
[@@_pd_attribute_bool] let pd_supports_sealing_public = 33uL
[@@_pd_attribute_bool] let pd_supports_rotate_context_handle = 34uL
[@@_pd_attribute_string] let pd_dice_derivation = 35uL
[@@_pd_attribute_string] let pd_asymmetric_derivation = 36uL
[@@_pd_attribute_string] let pd_symmetric_derivation = 37uL
[@@_pd_attribute_bool] let pd_supports_any_label = 38uL
[@@_pd_attribute_string] let pd_supported_labels = 39uL
[@@_pd_attribute_string] let pd_initial_derivation = 40uL
[@@_pd_attribute_string] let pd_input_format = 41uL
[@@_pd_attribute_bool] let pd_supports_internal_inputs = 42uL
[@@_pd_attribute_bool] let pd_supports_internal_dpe_info = 43uL
[@@_pd_attribute_bool] let pd_supports_internal_dpe_dice = 44uL
[@@_pd_attribute_string] let pd_internal_dpe_info_type = 45uL
[@@_pd_attribute_string] let pd_internal_dpe_dice_type = 46uL
[@@_pd_attribute_string] let pd_internal_inputs = 47uL
[@@_pd_attribute_bool] let pd_supports_certificates = 48uL
[@@_pd_attribute_number] let pd_max_certificate_size = 49uL
[@@_pd_attribute_number] let pd_max_certificate_chain_size = 50uL
[@@_pd_attribute_bool] let pd_appends_more_certificates = 51uL
[@@_pd_attribute_bool] let pd_supports_certificate_policies = 52uL
[@@_pd_attribute_bool] let pd_supports_policy_identity_init = 53uL
[@@_pd_attribute_bool] let pd_supports_policy_identity_loc = 54uL
[@@_pd_attribute_bool] let pd_supports_policy_attest_init = 55uL
[@@_pd_attribute_bool] let pd_supports_policy_attest_loc = 56uL
[@@_pd_attribute_bool] let pd_supports_policy_assert_init = 57uL
[@@_pd_attribute_bool] let pd_supports_policy_assert_loc = 58uL
[@@_pd_attribute_string] let pd_certificate_policies = 59uL
[@@_pd_attribute_bool] let pd_supports_eca_certificates = 60uL
[@@_pd_attribute_string] let pd_eca_certificate_format = 61uL
[@@_pd_attribute_string] let pd_leaf_certificate_format = 62uL
[@@_pd_attribute_string] let pd_public_key_format = 63uL
[@@_pd_attribute_bool] let pd_supports_external_key = 64uL
[@@_pd_attribute_string] let pd_to_be_signed_format = 65uL
[@@_pd_attribute_string] let pd_signature_format = 66uL
[@@_pd_attribute_bool] let pd_supports_symmetric_sign = 67uL
[@@_pd_attribute_bool] let pd_supports_asymmetric_unseal = 68uL
[@@_pd_attribute_bool] let pd_supports_unseal_policy = 69uL
[@@_pd_attribute_string] let pd_unseal_policy_format = 70uL

module T = FStar.Tactics

[@@noextract_to "krml"]
let t_create_choice_from_gen (attr: T.term) (f: T.term -> T.term -> T.term) : T.Tac T.term =
  let e = T.cur_env () in
  let l = T.lookup_attr attr e in
  let rec aux (accu: T.term) (l: list T.fv) : T.Tac T.term =
    match l with
    | [] -> accu
    | v :: l' ->
      let accu' = f accu (T.pack (T.Tv_FVar v)) in
      aux accu' l'
  in
  aux (`Cddl.t_always_false) l

[@@noextract_to "krml"]
let create_uint_choice_from (attr: T.term) : T.Tac unit =
  T.exact (t_create_choice_from_gen attr (fun accu t ->
    T.mk_e_app (`Cddl.t_choice) [
      T.mk_e_app (`Cddl.t_uint_literal) [
        t
      ];
      accu;
    ]
  ))

let pd_attribute_bool : Cddl.typ = _ by (create_uint_choice_from (`_pd_attribute_bool))
let pd_attribute_number : Cddl.typ = _ by (create_uint_choice_from (`_pd_attribute_number))
let pd_attribute_string : Cddl.typ = _ by (create_uint_choice_from (`_pd_attribute_string))

let profile_descriptor = Cddl.t_map (
  Cddl.map_group_cons_zero_or_more (pd_attribute_bool, Cddl.t_bool) false (* FIXME: really? *) (
  Cddl.map_group_cons_zero_or_more (pd_attribute_number, Cddl.uint) false (* FIXME: really? *) (
  Cddl.map_group_cons_zero_or_more (pd_attribute_string, Cddl.tstr) false (* FIXME: really? *) (
  Cddl.map_group_empty
))))

// Section 6.1

[@@_input_args] let get_profile_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false
  Cddl.map_group_empty
)

let get_profile_profile_descriptor = 1uL

[@@_output_args] let get_profile_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal get_profile_profile_descriptor, profile_descriptor) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false
  Cddl.map_group_empty
))

// Section 6.2

let open_session_initiator_handshake = 1uL
let open_session_is_migratable = 2uL

[@@_input_args] let open_session_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal open_session_initiator_handshake, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal open_session_is_migratable, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false (
  Cddl.map_group_empty
))))

let open_session_responder_handshake = 1uL

[@@_output_args] let open_session_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal open_session_responder_handshake, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false (
  Cddl.map_group_empty
)))

let responder_handshake_payload = Cddl.uint

// Section 6.3

[@@_input_args] let close_session_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false (
  Cddl.map_group_empty
))

[@@_output_args] let close_session_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false (
  Cddl.map_group_empty
))

// Section 6.4

let sync_session_session_id = 1uL
let sync_session_initiator_counter = 2uL

[@@_input_args] let sync_session_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sync_session_session_id, Cddl.uint) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sync_session_initiator_counter, Cddl.uint) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))

let sync_session_responder_counter = 1uL

[@@_output_args] let sync_session_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sync_session_responder_counter, Cddl.uint) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))

// Section 6.5

let export_session_session_id = 1uL
let export_session_importer_identity = 2uL
let export_session_psk = 3uL

[@@_input_args] let export_session_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal export_session_session_id, Cddl.uint) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal export_session_importer_identity, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal export_session_psk, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))))

let export_session_exported_data = 1uL

[@@_output_args] let export_session_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal export_session_exported_data, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))

// Section 6.6

let import_session_context_handle = 1uL
let import_session_retain_context = 2uL
let import_session_exported_data = 3uL
let import_session_psk = 4uL

[@@_input_args] let import_session_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal import_session_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal import_session_retain_context, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal import_session_exported_data, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal import_session_psk, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))))

let import_session_importer_identity = 1uL
let import_session_new_context_handle = 2uL

[@@_output_args] let import_session_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal import_session_importer_identity, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal import_session_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))

// Section 6.7

let initialize_context_simulation = 1uL
let initialize_context_use_default_context = 2uL
let initialize_context_seed = 3uL

[@@_input_args] let initialize_context_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal initialize_context_simulation, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal initialize_context_use_default_context, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal initialize_context_seed, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))))

let initialize_context_new_context_handle = 1uL

[@@_output_args] let initialize_context_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal initialize_context_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))

// Section 6.8

let derive_child_context_handle = 1uL
let derive_child_retain_parent_context = 2uL
let derive_child_allow_child_to_derive = 3uL
let derive_child_create_certificate = 4uL
let derive_child_new_session_initiator_handshake = 5uL
let derive_child_new_session_is_migratable = 6uL
let derive_child_input_data = 7uL
let derive_child_internal_inputs = 8uL

let internal_input_type_dpe_info = 1uL
let internal_input_type_dpe_dice = 2uL

let internal_input_type =
  Cddl.t_uint_literal internal_input_type_dpe_info `Cddl.t_choice`
  Cddl.t_uint_literal internal_input_type_dpe_dice

[@@_input_args] let derive_child_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_retain_parent_context, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_allow_child_to_derive, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_create_certificate, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_new_session_initiator_handshake, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_new_session_is_migratable, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_input_data, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_internal_inputs, Cddl.t_array3 (Cddl.array_group3_zero_or_more (Cddl.array_group3_item internal_input_type))) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))))))))

let derive_child_new_context_handle = 1uL
let derive_child_new_session_responder_handshake = 2uL
let derive_child_parent_context_handle = 3uL

[@@_output_args] let derive_child_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_new_session_responder_handshake, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_child_parent_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))))

// Section 6.9

let certify_key_context_handle = 1uL
let certify_key_retain_context = 2uL
let certify_key_public_key = 3uL
let certify_key_label = 4uL
let certify_key_policies = 5uL

let tcg_dice_kp_identityInit = 6uL
let tcg_dice_kp_identityLoc = 7uL
let tcg_dice_kp_attestInit = 8uL
let tcg_dice_kp_attestLoc = 9uL
let tcg_dice_kp_assertInit = 10uL
let tcg_dice_kp_assertLoc = 11uL

let policy_type =
  Cddl.t_uint_literal tcg_dice_kp_identityInit `Cddl.t_choice`
  Cddl.t_uint_literal tcg_dice_kp_identityLoc `Cddl.t_choice`
  Cddl.t_uint_literal tcg_dice_kp_attestInit `Cddl.t_choice`
  Cddl.t_uint_literal tcg_dice_kp_attestLoc `Cddl.t_choice`
  Cddl.t_uint_literal tcg_dice_kp_assertInit `Cddl.t_choice`
  Cddl.t_uint_literal tcg_dice_kp_assertLoc

[@@_input_args] let certify_key_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal certify_key_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal certify_key_retain_context, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal certify_key_public_key, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal certify_key_label, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal certify_key_policies, Cddl.t_array3 (Cddl.array_group3_zero_or_more (Cddl.array_group3_item policy_type))) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))))))

let certify_key_certificate_chain = 1uL
let certify_key_derived_public_key = 2uL
let certify_key_new_context_handle = 3uL

[@@_output_args] let certify_key_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal certify_key_certificate_chain, Cddl.t_array3 (Cddl.array_group3_one_or_more (Cddl.array_group3_item Cddl.bytes))) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal certify_key_derived_public_key, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal certify_key_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))))

// Section 6.10

let sign_context_handle = 1uL
let sign_retain_context = 2uL
let sign_label = 3uL
let sign_is_symmetric = 4uL
let sign_to_be_signed = 5uL

[@@_input_args] let sign_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sign_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sign_retain_context, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sign_label, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sign_is_symmetric, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sign_to_be_signed, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))))))

let sign_signature = 1uL
let sign_new_context_handle = 2uL

[@@_output_args] let sign_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sign_signature, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal sign_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))

// Section 6.11

let seal_context_handle = 1uL
let seal_retain_context = 2uL
let seal_unseal_policy = 3uL
let seal_label = 4uL
let seal_data_to_seal = 5uL

[@@_input_args] let seal_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal seal_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal seal_retain_context, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal seal_unseal_policy, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal seal_label, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal seal_data_to_seal, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))))))

let seal_sealed_data = 1uL
let seal_new_context_handle = 2uL

[@@_output_args] let seal_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal seal_sealed_data, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal seal_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))

// Section 6.12

let unseal_context_handle = 1uL
let unseal_retain_context = 2uL
let unseal_is_asymmetric = 3uL
let unseal_label = 4uL
let unseal_data_to_unseal = 5uL

[@@_input_args] let unseal_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal unseal_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal unseal_retain_context, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal unseal_is_asymmetric, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal unseal_label, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal unseal_data_to_unseal, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))))))

let unseal_unsealed_data = 1uL
let unseal_new_context_handle = 2uL

[@@_output_args] let unseal_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal unseal_unsealed_data, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal unseal_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))

// Section 6.13

let derive_sealing_context_handle = 1uL
let derive_sealing_retain_context = 2uL
let derive_sealing_unseal_policy = 3uL
let derive_sealing_label = 4uL

[@@_input_args] let derive_sealing_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_sealing_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_sealing_retain_context, Cddl.t_bool) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_sealing_unseal_policy, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_sealing_label, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))))

let derive_sealing_derived_public_key = 1uL
let derive_sealing_new_context_handle = 2uL

[@@_output_args] let derive_sealing_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_sealing_derived_public_key, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal derive_sealing_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)))

// Section 6.14

let rotate_context_handle_context_handle = 1uL

[@@_input_args] let rotate_context_handle_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal rotate_context_handle_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))

let rotate_context_handle_new_context_handle = 2uL

[@@_output_args] let rotate_context_handle_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal rotate_context_handle_new_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))

// Section 6.15

let destroy_context_context_handle = 1uL

[@@_input_args] let destroy_context_input_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_one (Cddl.t_uint_literal destroy_context_context_handle, Cddl.bytes) false (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
))

[@@_output_args] let destroy_context_output_args = Cddl.t_map (
  Cddl.map_group_cons_zero_or_more (Cddl.uint, Cddl.any) false Cddl.map_group_empty
)

// Section 5.9.4: summary

[@@noextract_to "krml"]
let create_choice_from (attr: T.term) : T.Tac unit =
  T.exact (t_create_choice_from_gen attr (fun accu t ->
    T.mk_e_app (`Cddl.t_choice) [
      t;
      accu;
    ]
  ))

let input_args : Cddl.typ = _ by (create_choice_from (`_input_args))
let output_args : Cddl.typ = _ by (create_choice_from (`_output_args))

let command_message = Cddl.t_array3 (
  Cddl.array_group3_item (* command_id *) command_id `Cddl.array_group3_concat`
  Cddl.array_group3_item (* input_args *) input_args
)

let response_message = Cddl.t_array3 (
  Cddl.array_group3_item (* error_code *) error_code `Cddl.array_group3_concat`
  Cddl.array_group3_item (* output_args *) output_args
)