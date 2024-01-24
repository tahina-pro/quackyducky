#light "off"
module FStar_Monotonic_HyperStack
open Prims
open FStar_Pervasives

let is_in : unit  ->  FStar_Monotonic_HyperHeap.hmap  ->  Prims.bool = (fun ( r  :  unit ) ( h  :  FStar_Monotonic_HyperHeap.hmap ) -> (FStar_Map.contains h ()))


let is_heap_color : Prims.int  ->  Prims.bool = (fun ( c  :  Prims.int ) -> (c <= (Prims.parse_int "0")))


type sid =
unit


type map_invariant_predicate =
unit


type downward_closed_predicate =
unit


type tip_top_predicate =
unit


type rid_ctr_pred_predicate =
unit


type map_invariant =
unit


type downward_closed =
unit


type tip_top =
unit


type rid_ctr_pred =
unit


type is_tip =
unit


type is_wf_with_ctr_and_tip =
unit

type mem' =
| HS of Prims.int * FStar_Monotonic_HyperHeap.hmap * unit


let uu___is_HS : mem'  ->  Prims.bool = (fun ( projectee  :  mem' ) -> true)


let __proj__HS__item__rid_ctr : mem'  ->  Prims.int = (fun ( projectee  :  mem' ) -> (match (projectee) with
| HS (rid_ctr, h, tip) -> begin
rid_ctr
end))


let __proj__HS__item__h : mem'  ->  FStar_Monotonic_HyperHeap.hmap = (fun ( projectee  :  mem' ) -> (match (projectee) with
| HS (rid_ctr, h, tip) -> begin
h
end))





let mk_mem : Prims.int  ->  FStar_Monotonic_HyperHeap.hmap  ->  unit  ->  mem' = (fun ( rid_ctr  :  Prims.int ) ( h  :  FStar_Monotonic_HyperHeap.hmap ) ( tip  :  unit ) -> HS (rid_ctr, h, ()))


let get_hmap : mem'  ->  FStar_Monotonic_HyperHeap.hmap = (fun ( m  :  mem' ) -> (__proj__HS__item__h m))


let get_rid_ctr : mem'  ->  Prims.int = (fun ( m  :  mem' ) -> (__proj__HS__item__rid_ctr m))





type mem =
mem'


let empty_mem : mem = (

let empty_map = (FStar_Map.restrict (FStar_Set.empty ()) (FStar_Map.const1 FStar_Monotonic_Heap.emp))
in (

let h = (FStar_Map.upd empty_map () FStar_Monotonic_Heap.emp)
in (mk_mem (Prims.parse_int "1") h ())))


type poppable =
unit


let remove_elt = (fun ( s  :  'a FStar_Set.set ) ( x  :  'a ) -> (FStar_Set.intersect s (FStar_Set.complement (FStar_Set.singleton x))))


type popped =
unit


let pop : mem  ->  mem = (fun ( m0  :  mem ) -> (

let uu___ = (((get_hmap m0)), (()), ((get_rid_ctr m0)))
in (match (uu___) with
| (h0, tip0, rid_ctr0) -> begin
(

let dom = (remove_elt (FStar_Map.domain h0) ())
in (

let h1 = (FStar_Map.restrict dom h0)
in (mk_mem rid_ctr0 h1 ())))
end)))

type ('a, 'rel) mreference' =
| MkRef of unit * 'a FStar_Monotonic_Heap.mref


let uu___is_MkRef = (fun ( projectee  :  ('a, 'rel) mreference' ) -> true)





let __proj__MkRef__item__ref = (fun ( projectee  :  ('a, 'rel) mreference' ) -> (match (projectee) with
| MkRef (frame, ref) -> begin
ref
end))


type ('a, 'rel) mreference =
('a, 'rel) mreference'





let mk_mreference = (fun ( id  :  unit ) ( r  :  'a FStar_Monotonic_Heap.mref ) -> MkRef ((), r))


let as_ref = (fun ( x  :  ('uuuuu, 'uuuuu1) mreference ) -> (__proj__MkRef__item__ref x))


type ('a, 'rel) mstackref =
('a, 'rel) mreference


type ('a, 'rel) mref =
('a, 'rel) mreference


type ('a, 'rel) mmmstackref =
('a, 'rel) mreference


type ('a, 'rel) mmmref =
('a, 'rel) mreference


type ('a, 'rel) s_mref =
('a, 'rel) mreference


let live_region : mem  ->  unit  ->  Prims.bool = (fun ( m  :  mem ) ( i  :  unit ) -> (FStar_Map.contains (get_hmap m) ()))


type contains =
unit


type unused_in =
unit


type ('a, 'rel) contains_ref_in_its_region =
('a, 'rel, unit, unit) FStar_Monotonic_Heap.contains


type fresh_ref =
unit


type fresh_region =
unit


let alloc = (fun ( id  :  unit ) ( init  :  'a ) ( mm  :  Prims.bool ) ( m  :  mem ) -> (

let uu___ = (((get_hmap m)), ((get_rid_ctr m)), (()))
in (match (uu___) with
| (h, rid_ctr, tip) -> begin
(

let uu___1 = (FStar_Monotonic_Heap.alloc (FStar_Map.sel h ()) init mm)
in (match (uu___1) with
| (r, id_h) -> begin
(

let h1 = (FStar_Map.upd h () id_h)
in (((mk_mreference () r)), ((mk_mem rid_ctr h1 ()))))
end))
end)))


let free = (fun ( r  :  ('a, 'rel) mreference ) ( m  :  mem ) -> (

let uu___ = (((get_hmap m)), ((get_rid_ctr m)), (()))
in (match (uu___) with
| (h, rid_ctr, tip) -> begin
(

let i_h = (FStar_Map.sel h ())
in (

let i_h1 = (FStar_Monotonic_Heap.free_mm i_h (as_ref r))
in (

let h1 = (FStar_Map.upd h () i_h1)
in (mk_mem rid_ctr h1 ()))))
end)))


let upd_tot = (fun ( m  :  mem ) ( r  :  ('a, 'rel) mreference ) ( v  :  'a ) -> (

let uu___ = (((get_hmap m)), ((get_rid_ctr m)), (()))
in (match (uu___) with
| (h, rid_ctr, tip) -> begin
(

let i_h = (FStar_Map.sel h ())
in (

let i_h1 = (FStar_Monotonic_Heap.upd_tot i_h (as_ref r) v)
in (

let h1 = (FStar_Map.upd h () i_h1)
in (mk_mem rid_ctr h1 ()))))
end)))


let sel_tot = (fun ( m  :  mem ) ( r  :  ('a, 'rel) mreference ) -> (FStar_Monotonic_Heap.sel_tot (FStar_Map.sel (get_hmap m) ()) (as_ref r)))


type fresh_frame =
unit


let hs_push_frame : mem  ->  mem = (fun ( m  :  mem ) -> (

let uu___ = (((get_hmap m)), ((get_rid_ctr m)), (()))
in (match (uu___) with
| (h, rid_ctr, tip) -> begin
(

let h1 = (FStar_Map.upd h () FStar_Monotonic_Heap.emp)
in (mk_mem (rid_ctr + (Prims.parse_int "1")) h1 ()))
end)))


let new_eternal_region : mem  ->  unit  ->  Prims.int FStar_Pervasives_Native.option  ->  (unit * mem) = (fun ( m  :  mem ) ( parent  :  unit ) ( c  :  Prims.int FStar_Pervasives_Native.option ) -> (

let uu___ = (((get_hmap m)), ((get_rid_ctr m)), (()))
in (match (uu___) with
| (h, rid_ctr, tip) -> begin
(

let h1 = (FStar_Map.upd h () FStar_Monotonic_Heap.emp)
in ((()), ((mk_mem (rid_ctr + (Prims.parse_int "1")) h1 ()))))
end)))


let new_freeable_heap_region : mem  ->  unit  ->  (unit * mem) = (fun ( m  :  mem ) ( parent  :  unit ) -> (

let uu___ = (((get_hmap m)), ((get_rid_ctr m)), (()))
in (match (uu___) with
| (h, rid_ctr, tip) -> begin
(

let h1 = (FStar_Map.upd h () FStar_Monotonic_Heap.emp)
in ((()), ((mk_mem (rid_ctr + (Prims.parse_int "1")) h1 ()))))
end)))


let free_heap_region : mem  ->  unit  ->  mem = (fun ( m0  :  mem ) ( r  :  unit ) -> (

let uu___ = (((get_hmap m0)), ((get_rid_ctr m0)))
in (match (uu___) with
| (h0, rid_ctr0) -> begin
(

let dom = (remove_elt (FStar_Map.domain h0) ())
in (

let h1 = (FStar_Map.restrict dom h0)
in (mk_mem (get_rid_ctr m0) h1 ())))
end)))


type modifies =
unit


type modifies_transitively =
unit


type heap_only =
unit


let top_frame : mem  ->  FStar_Monotonic_Heap.heap = (fun ( m  :  mem ) -> (FStar_Map.sel (get_hmap m) ()))


type modifies_one =
unit


type modifies_ref =
unit

type some_ref =
| Ref of unit * unit * (obj, obj) mreference


let uu___is_Ref : some_ref  ->  Prims.bool = (fun ( projectee  :  some_ref ) -> true)


let __proj__Ref__item___2 : some_ref  ->  (unit, unit) mreference = (fun ( uu___  :  some_ref ) -> ((fun ( projectee  :  some_ref ) -> (match (projectee) with
| Ref (a, rel, _2) -> begin
(Prims.unsafe_coerce _2)
end)) uu___))


type some_refs =
some_ref Prims.list


let rec regions_of_some_refs : some_refs  ->  unit FStar_Set.set = (fun ( rs  :  some_refs ) -> (match (rs) with
| [] -> begin
(FStar_Set.empty ())
end
| (Ref (uu___, uu___1, r))::tl -> begin
(FStar_Set.union (FStar_Set.singleton ()) (regions_of_some_refs tl))
end))


type modifies_some_refs =
obj


let norm_steps : FStar_Pervasives.norm_step Prims.list = (FStar_Pervasives.iota)::(FStar_Pervasives.zeta)::(FStar_Pervasives.delta)::((FStar_Pervasives.delta_only (("FStar.Monotonic.HyperStack.regions_of_some_refs")::("FStar.Monotonic.HyperStack.refs_in_region")::("FStar.Monotonic.HyperStack.modifies_some_refs")::[])))::(FStar_Pervasives.primops)::[]


type mods =
unit

type aref =
| ARef of unit * FStar_Monotonic_Heap.aref


let uu___is_ARef : aref  ->  Prims.bool = (fun ( projectee  :  aref ) -> true)





let __proj__ARef__item__aref_aref : aref  ->  FStar_Monotonic_Heap.aref = (fun ( projectee  :  aref ) -> (match (projectee) with
| ARef (aref_region, aref_aref) -> begin
aref_aref
end))


let dummy_aref : aref = ARef ((), FStar_Monotonic_Heap.dummy_aref)


let aref_of = (fun ( r  :  ('uuuuu, 'uuuuu1) mreference ) -> ARef ((), (FStar_Monotonic_Heap.aref_of (as_ref r))))


type aref_unused_in =
unit


type aref_live_at =
unit


let reference_of : mem  ->  aref  ->  unit  ->  unit  ->  (obj, obj) mreference = (fun ( h  :  mem ) ( a  :  aref ) ( v  :  unit ) ( rel  :  unit ) -> MkRef ((), (FStar_Monotonic_Heap.ref_of (FStar_Map.sel (__proj__HS__item__h h) ()) (__proj__ARef__item__aref_aref a) () ())))




