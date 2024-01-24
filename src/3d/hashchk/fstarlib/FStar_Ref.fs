#light "off"
module FStar_Ref
open Prims
open FStar_Pervasives

type 'a contains =
('a, unit, unit, unit) FStar_Monotonic_Heap.contains


type 'a unused_in =
('a, unit, unit, unit) FStar_Monotonic_Heap.unused_in


type fresh =
unit


let recall = (fun ( r  :  'uuuuu FStar_ST.ref ) -> (FStar_ST.recall r))


let alloc = (fun ( init  :  'uuuuu ) -> (FStar_ST.alloc init))


let read = (fun ( r  :  'uuuuu FStar_ST.ref ) -> (FStar_ST.read r))


let write = (fun ( r  :  'uuuuu FStar_ST.ref ) ( v  :  'uuuuu ) -> (FStar_ST.write r v))


let op_Bang = (fun ( r  :  'uuuuu FStar_ST.ref ) -> (read r))


let op_Colon_Equals = (fun ( r  :  'uuuuu FStar_ST.ref ) ( v  :  'uuuuu ) -> (write r v))




