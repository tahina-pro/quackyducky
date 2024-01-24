#light "off"
module FStar_HyperStack
open Prims
open FStar_Pervasives

type 'a reference =
('a, unit) FStar_Monotonic_HyperStack.mreference


type 'a stackref =
('a, unit) FStar_Monotonic_HyperStack.mstackref


type 'a ref =
('a, unit) FStar_Monotonic_HyperStack.mref


type 'a mmstackref =
('a, unit) FStar_Monotonic_HyperStack.mmmstackref


type 'a mmref =
('a, unit) FStar_Monotonic_HyperStack.mmmref


type 'a s_ref =
('a, unit) FStar_Monotonic_HyperStack.s_mref




