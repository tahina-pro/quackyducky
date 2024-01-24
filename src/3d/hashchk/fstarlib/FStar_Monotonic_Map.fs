#light "off"
module FStar_Monotonic_Map
open Prims
open FStar_Pervasives

type ('a, 'b) map' =
'a  ->  'b FStar_Pervasives_Native.option


type ('a, 'b) map =
('a, 'b) map'


let upd = (fun ( m  :  ('a, 'b) map' ) ( x  :  'a ) ( y  :  'b ) ( z  :  'a ) -> (match ((Prims.op_Equality x z)) with
| true -> begin
FStar_Pervasives_Native.Some (y)
end
| uu___ -> begin
(m z)
end))


let sel = (fun ( m  :  ('a, 'b) map' ) ( x  :  'a ) -> (m x))


type grows_aux =
unit


type grows =
unit


type ('a, 'b) t =
(('a, 'b) map, unit) FStar_HyperStack_ST.m_rref


let empty_map = (fun ( x  :  'a ) -> FStar_Pervasives_Native.None)


type rid =
unit


let alloc : unit  ->  unit  ->  unit  ->  unit  ->  (obj, obj) t = (fun ( r  :  unit ) ( a  :  unit ) ( b  :  unit ) ( inv  :  unit ) -> (FStar_HyperStack_ST.ralloc () empty_map))


type defined =
unit


type contains =
unit


type fresh =
unit


let extend : unit  ->  unit  ->  unit  ->  unit  ->  (obj, obj) t  ->  obj  ->  obj  ->  unit = (fun ( r  :  unit ) ( a  :  unit ) ( b  :  unit ) ( inv  :  unit ) ( m  :  (obj, obj) t ) ( x  :  obj ) ( y  :  obj ) -> ((FStar_HyperStack_ST.recall m);
(

let cur = (FStar_HyperStack_ST.op_Bang m)
in ((FStar_HyperStack_ST.op_Colon_Equals m (upd cur x y));
(FStar_HyperStack_ST.mr_witness () () () (Prims.unsafe_coerce m) ());
(FStar_HyperStack_ST.mr_witness () () () (Prims.unsafe_coerce m) ());
));
))


let lookup : unit  ->  unit  ->  unit  ->  unit  ->  (obj, obj) t  ->  obj  ->  obj FStar_Pervasives_Native.option = (fun ( r  :  unit ) ( a  :  unit ) ( b  :  unit ) ( inv  :  unit ) ( m  :  (obj, obj) t ) ( x  :  obj ) -> (

let y = (

let uu___ = (FStar_HyperStack_ST.op_Bang m)
in (sel uu___ x))
in (match (y) with
| FStar_Pervasives_Native.None -> begin
y
end
| FStar_Pervasives_Native.Some (b1) -> begin
((FStar_HyperStack_ST.mr_witness () () () (Prims.unsafe_coerce m) ());
(FStar_HyperStack_ST.mr_witness () () () (Prims.unsafe_coerce m) ());
y;
)
end)))




