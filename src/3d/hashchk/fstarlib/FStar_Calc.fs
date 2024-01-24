#light "off"
module FStar_Calc
open Prims
open FStar_Pervasives
type ('a, 'dummyV0, 'dummyV1, 'dummyV2) calc_chain =
| CalcRefl of 'a
| CalcStep of unit Prims.list * unit * 'a * 'a * 'a * ('a, unit, unit, unit) calc_chain * unit


let uu___is_CalcRefl = (fun ( uu___  :  unit Prims.list ) ( uu___1  :  'a ) ( uu___2  :  'a ) ( projectee  :  ('a, unit, unit, unit) calc_chain ) -> (match (projectee) with
| CalcRefl (x) -> begin
true
end
| uu___3 -> begin
false
end))


let __proj__CalcRefl__item__x = (fun ( uu___  :  unit Prims.list ) ( uu___1  :  'a ) ( uu___2  :  'a ) ( projectee  :  ('a, unit, unit, unit) calc_chain ) -> (match (projectee) with
| CalcRefl (x) -> begin
x
end))


let uu___is_CalcStep = (fun ( uu___  :  unit Prims.list ) ( uu___1  :  'a ) ( uu___2  :  'a ) ( projectee  :  ('a, unit, unit, unit) calc_chain ) -> (match (projectee) with
| CalcStep (rs, p, x, y, z, _5, _6) -> begin
true
end
| uu___3 -> begin
false
end))


let __proj__CalcStep__item__rs = (fun ( uu___  :  unit Prims.list ) ( uu___1  :  'a ) ( uu___2  :  'a ) ( projectee  :  ('a, unit, unit, unit) calc_chain ) -> (match (projectee) with
| CalcStep (rs, p, x, y, z, _5, _6) -> begin
rs
end))


let __proj__CalcStep__item__x = (fun ( uu___  :  unit Prims.list ) ( uu___1  :  'a ) ( uu___2  :  'a ) ( projectee  :  ('a, unit, unit, unit) calc_chain ) -> (match (projectee) with
| CalcStep (rs, p, x, y, z, _5, _6) -> begin
x
end))


let __proj__CalcStep__item__y = (fun ( uu___  :  unit Prims.list ) ( uu___1  :  'a ) ( uu___2  :  'a ) ( projectee  :  ('a, unit, unit, unit) calc_chain ) -> (match (projectee) with
| CalcStep (rs, p, x, y, z, _5, _6) -> begin
y
end))


let __proj__CalcStep__item__z = (fun ( uu___  :  unit Prims.list ) ( uu___1  :  'a ) ( uu___2  :  'a ) ( projectee  :  ('a, unit, unit, unit) calc_chain ) -> (match (projectee) with
| CalcStep (rs, p, x, y, z, _5, _6) -> begin
z
end))


let __proj__CalcStep__item___5 = (fun ( uu___  :  unit Prims.list ) ( uu___1  :  'a ) ( uu___2  :  'a ) ( projectee  :  ('a, unit, unit, unit) calc_chain ) -> (match (projectee) with
| CalcStep (rs, p, x, y, z, _5, _6) -> begin
_5
end))


type calc_chain_related =
obj


type calc_chain_compatible =
unit


type calc_pack =
unit


let _calc_init = (fun ( x  :  'a ) -> CalcRefl (x))










