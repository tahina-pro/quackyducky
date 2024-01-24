#light "off"
module FStar_FunctionalExtensionality
open Prims
open FStar_Pervasives

type ('a, 'b) arrow =
'a  ->  'b


type ('a, 'b) efun =
'a  ->  'b


type feq =
unit


let on_domain = (fun ( f  :  'a  ->  'b ) ( x  :  'a ) -> (f x))


type is_restricted =
unit


type ('a, 'b) restricted_t =
'a  ->  'b


type ('a, 'b) op_Hat_Subtraction_Greater =
('a, 'b) restricted_t


let on_dom = (fun ( f  :  'a  ->  'b ) ( x  :  'a ) -> (f x))


let on = (fun ( f  :  'a  ->  'b ) ( x  :  'a ) -> (f x))


type arrow_g =
unit


type efun_g =
unit


type feq_g =
unit





type is_restricted_g =
unit


type restricted_g_t =
unit


type op_Hat_Subtraction_Greater_Greater =
unit










