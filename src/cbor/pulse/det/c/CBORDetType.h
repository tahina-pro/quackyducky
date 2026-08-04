

#ifndef CBORDetType_H
#define CBORDetType_H

#if defined(__cplusplus)
extern "C" {
#endif

#include "krmllib.h"

typedef struct CBOR_Spec_Raw_Base_raw_uint64_s
{
  uint8_t size;
  uint64_t value;
}
CBOR_Spec_Raw_Base_raw_uint64;

typedef struct CBOR_Pulse_Raw_Slice_byte_slice_s
{
  uint8_t *elt;
  size_t len;
}
CBOR_Pulse_Raw_Slice_byte_slice;

typedef struct CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator_s
{
  CBOR_Pulse_Raw_Slice_byte_slice s;
  uint64_t len;
}
CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator;

typedef struct cbor_serialized_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_serialized_header;
  CBOR_Pulse_Raw_Slice_byte_slice cbor_serialized_payload;
}
cbor_serialized;

typedef struct cbor_int_s
{
  uint8_t cbor_int_type;
  uint8_t cbor_int_size;
  uint64_t cbor_int_value;
}
cbor_int;

typedef struct cbor_string_s
{
  uint8_t cbor_string_type;
  uint8_t cbor_string_size;
  CBOR_Pulse_Raw_Slice_byte_slice cbor_string_ptr;
}
cbor_string;

typedef struct cbor_raw_s cbor_raw;

typedef struct cbor_tagged_s
{
  CBOR_Spec_Raw_Base_raw_uint64 cbor_tagged_tag;
  cbor_raw *cbor_tagged_ptr;
}
cbor_tagged;

typedef struct Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw_s
{
  cbor_raw *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct cbor_array_s
{
  uint8_t cbor_array_length_size;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw cbor_array_ptr;
}
cbor_array;

typedef struct cbor_map_entry_s cbor_map_entry;

typedef struct Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  cbor_map_entry *elt;
  size_t len;
}
Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry;

typedef struct cbor_map_s
{
  uint8_t cbor_map_length_size;
  Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry cbor_map_ptr;
}
cbor_map;

typedef struct cbor_raw_s cbor_raw;

#define LowParse_PulseParse_Iterator_Type_Empty 0
#define LowParse_PulseParse_Iterator_Type_Singleton 1
#define LowParse_PulseParse_Iterator_Type_Slice 2
#define LowParse_PulseParse_Iterator_Type_Serialized 3

typedef uint8_t
LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags;

typedef struct
LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags
  tag;
  union {
    cbor_raw *case_Singleton;
    struct
    {
      Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw ss;
      uint64_t count;
    }
    case_Slice;
    struct
    {
      uint64_t count;
      CBOR_Pulse_Raw_Slice_byte_slice payload;
    }
    case_Serialized;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_s
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw;

#define LowParse_PulseParse_Iterator_Type_Base 0
#define LowParse_PulseParse_Iterator_Type_Append 1

typedef uint8_t
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags;

typedef struct
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  union {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw
    case_Base;
    struct
    {
      uint64_t cb;
      uint64_t ca;
      uint64_t tot;
      uint64_t ob;
      LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw *before;
      uint64_t oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw *after;
    }
    case_Append;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw;

typedef struct cbor_mixed_list_array_s
{
  uint8_t cbor_array_gen_length_size;
  LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw
  cbor_array_gen_ptr;
}
cbor_mixed_list_array;

typedef struct
LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags
  tag;
  union {
    cbor_map_entry *case_Singleton;
    struct
    {
      Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry ss;
      uint64_t count;
    }
    case_Slice;
    struct
    {
      uint64_t count;
      CBOR_Pulse_Raw_Slice_byte_slice payload;
    }
    case_Serialized;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry;

typedef struct
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry_s
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry;

typedef struct
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  union {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
    case_Base;
    struct
    {
      uint64_t cb;
      uint64_t ca;
      uint64_t tot;
      uint64_t ob;
      LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
      *before;
      uint64_t oa;
      LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
      *after;
    }
    case_Append;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry;

typedef struct cbor_mixed_list_map_s
{
  uint8_t cbor_map_gen_length_size;
  LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
  cbor_map_gen_ptr;
}
cbor_mixed_list_map;

#define CBOR_Case_Int 0
#define CBOR_Case_Simple 1
#define CBOR_Case_String 2
#define CBOR_Case_Tagged 3
#define CBOR_Case_Array 4
#define CBOR_Case_Map 5
#define CBOR_Case_Serialized_Tagged 6
#define CBOR_Case_Serialized_Array 7
#define CBOR_Case_Serialized_Map 8
#define CBOR_Case_Array_Gen 9
#define CBOR_Case_Map_Gen 10

typedef uint8_t cbor_raw_tags;

typedef struct cbor_raw_s
{
  cbor_raw_tags tag;
  union {
    cbor_int case_CBOR_Case_Int;
    uint8_t case_CBOR_Case_Simple;
    cbor_string case_CBOR_Case_String;
    cbor_tagged case_CBOR_Case_Tagged;
    cbor_array case_CBOR_Case_Array;
    cbor_map case_CBOR_Case_Map;
    cbor_serialized case_CBOR_Case_Serialized_Tagged;
    cbor_serialized case_CBOR_Case_Serialized_Array;
    cbor_serialized case_CBOR_Case_Serialized_Map;
    cbor_mixed_list_array case_CBOR_Case_Array_Gen;
    cbor_mixed_list_map case_CBOR_Case_Map_Gen;
  }
  ;
}
cbor_raw;

typedef struct cbor_map_entry_s
{
  cbor_raw cbor_map_entry_key;
  cbor_raw cbor_map_entry_value;
}
cbor_map_entry;

#define LowParse_PulseParse_Iterator_Type_IBase 0
#define LowParse_PulseParse_Iterator_Type_IPair 1

typedef uint8_t
LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags;

typedef struct
LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_s
{
  LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  union {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw
    case_IBase;
    struct
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw
      before;
      LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw after;
    }
    case_IPair;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw;

#define CBOR_Raw_Iterator_Slice 0
#define CBOR_Raw_Iterator_Serialized 1
#define CBOR_Raw_Iterator_Mixed 2

typedef uint8_t cbor_array_iterator_tags;

typedef struct cbor_array_iterator_s
{
  cbor_array_iterator_tags tag;
  union {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_raw case_CBOR_Raw_Iterator_Slice;
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator case_CBOR_Raw_Iterator_Serialized;
    LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw
    case_CBOR_Raw_Iterator_Mixed;
  }
  ;
}
cbor_array_iterator;

typedef struct
LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry_s
{
  LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw_tags tag;
  union {
    LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
    case_IBase;
    struct
    {
      LowParse_PulseParse_Iterator_Type_base_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
      before;
      LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
      after;
    }
    case_IPair;
  }
  ;
}
LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry;

typedef struct cbor_map_iterator_s
{
  cbor_array_iterator_tags tag;
  union {
    Pulse_Lib_Slice_slice__CBOR_Pulse_Raw_Type_cbor_map_entry case_CBOR_Raw_Iterator_Slice;
    CBOR_Pulse_Raw_Iterator_Base_cbor_raw_serialized_iterator case_CBOR_Raw_Iterator_Serialized;
    LowParse_PulseParse_Iterator_Type_iterator__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
    case_CBOR_Raw_Iterator_Mixed;
  }
  ;
}
cbor_map_iterator;

typedef cbor_raw cbor_det_t;

typedef cbor_map_entry cbor_det_map_entry_t;

typedef cbor_array_iterator cbor_det_array_iterator_t;

typedef cbor_map_iterator cbor_det_map_iterator_t;

typedef LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_raw
cbor_det_array_append_cell_t;

typedef LowParse_PulseParse_Iterator_Type_mixed_list__uint64_t_CBOR_Pulse_Raw_Type_cbor_map_entry
cbor_det_map_entry_insert_cell_t;

typedef cbor_mixed_list_array cbor_det_array_t;

#if defined(__cplusplus)
}
#endif

#define CBORDetType_H_DEFINED
#endif /* CBORDetType_H */
