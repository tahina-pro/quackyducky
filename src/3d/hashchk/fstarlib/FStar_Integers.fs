#light "off"
module FStar_Integers
open Prims
open FStar_Pervasives

let norm = (fun ( x  :  'a ) -> x)

type width =
| W8
| W16
| W32
| W64
| W128
| Winfinite


let uu___is_W8 : width  ->  Prims.bool = (fun ( projectee  :  width ) -> (match (projectee) with
| W8 -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_W16 : width  ->  Prims.bool = (fun ( projectee  :  width ) -> (match (projectee) with
| W16 -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_W32 : width  ->  Prims.bool = (fun ( projectee  :  width ) -> (match (projectee) with
| W32 -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_W64 : width  ->  Prims.bool = (fun ( projectee  :  width ) -> (match (projectee) with
| W64 -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_W128 : width  ->  Prims.bool = (fun ( projectee  :  width ) -> (match (projectee) with
| W128 -> begin
true
end
| uu___ -> begin
false
end))


let uu___is_Winfinite : width  ->  Prims.bool = (fun ( projectee  :  width ) -> (match (projectee) with
| Winfinite -> begin
true
end
| uu___ -> begin
false
end))


let nat_of_width : width  ->  Prims.int FStar_Pervasives_Native.option = (fun ( uu___  :  width ) -> (match (uu___) with
| W8 -> begin
FStar_Pervasives_Native.Some ((Prims.parse_int "8"))
end
| W16 -> begin
FStar_Pervasives_Native.Some ((Prims.parse_int "16"))
end
| W32 -> begin
FStar_Pervasives_Native.Some ((Prims.parse_int "32"))
end
| W64 -> begin
FStar_Pervasives_Native.Some ((Prims.parse_int "64"))
end
| W128 -> begin
FStar_Pervasives_Native.Some ((Prims.parse_int "128"))
end
| Winfinite -> begin
FStar_Pervasives_Native.None
end))


type fixed_width =
width


let nat_of_fixed_width : fixed_width  ->  Prims.int = (fun ( w  :  fixed_width ) -> (match ((nat_of_width w)) with
| FStar_Pervasives_Native.Some (v) -> begin
v
end))

type signed_width =
| Signed of width
| Unsigned of fixed_width


let uu___is_Signed : signed_width  ->  Prims.bool = (fun ( projectee  :  signed_width ) -> (match (projectee) with
| Signed (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__Signed__item___0 : signed_width  ->  width = (fun ( projectee  :  signed_width ) -> (match (projectee) with
| Signed (_0) -> begin
_0
end))


let uu___is_Unsigned : signed_width  ->  Prims.bool = (fun ( projectee  :  signed_width ) -> (match (projectee) with
| Unsigned (_0) -> begin
true
end
| uu___ -> begin
false
end))


let __proj__Unsigned__item___0 : signed_width  ->  fixed_width = (fun ( projectee  :  signed_width ) -> (match (projectee) with
| Unsigned (_0) -> begin
_0
end))


let width_of_sw : signed_width  ->  width = (fun ( uu___  :  signed_width ) -> (match (uu___) with
| Signed (w) -> begin
w
end
| Unsigned (w) -> begin
w
end))


type within_bounds =
obj


type uint_8 =
FStar_UInt8.t


type uint_16 =
FStar_UInt16.t


type uint_32 =
FStar_UInt32.t


type uint_64 =
FStar_UInt64.t


type int =
Prims.int


type int_8 =
FStar_Int8.t


type int_16 =
FStar_Int16.t


type int_32 =
FStar_Int32.t


type int_64 =
FStar_Int64.t


type int_128 =
FStar_Int128.t


type ok =
obj


type nat =
Prims.int


type pos =
Prims.int


let f_int : Prims.int  ->  Prims.int  ->  Prims.int = (fun ( x  :  Prims.int ) ( y  :  Prims.int ) -> (x + y))


let f_nat : Prims.int  ->  Prims.int  ->  Prims.int = (fun ( x  :  Prims.int ) ( y  :  Prims.int ) -> (x + y))


let f_nat_int_pos : Prims.int  ->  Prims.int  ->  Prims.int  ->  Prims.int = (fun ( x  :  Prims.int ) ( y  :  Prims.int ) ( z  :  Prims.int ) -> ((x + y) + z))


let f_uint_8 : FStar_UInt8.t  ->  FStar_UInt8.t  ->  FStar_UInt8.t = (fun ( x  :  FStar_UInt8.t ) ( y  :  FStar_UInt8.t ) -> (FStar_UInt8.add x y))


let f_int_16 : FStar_Int16.t  ->  FStar_Int16.t  ->  FStar_Int16.t = (fun ( x  :  FStar_Int16.t ) ( y  :  FStar_Int16.t ) -> (FStar_Int16.add x y))


let g : FStar_UInt32.t  ->  FStar_UInt32.t  ->  FStar_UInt32.t = (fun ( x  :  FStar_UInt32.t ) ( y  :  FStar_UInt32.t ) -> (FStar_UInt32.add x (FStar_UInt32.mul y y)))


let h : Prims.nat  ->  Prims.nat  ->  Prims.int = (fun ( x  :  Prims.nat ) ( y  :  Prims.nat ) -> (x + y))


let i : Prims.nat  ->  Prims.nat  ->  Prims.int = (fun ( x  :  Prims.nat ) ( y  :  Prims.nat ) -> (x + y))


let j : Prims.int  ->  Prims.nat  ->  Prims.int = (fun ( x  :  Prims.int ) ( y  :  Prims.nat ) -> (x - y))


let k : Prims.int  ->  Prims.int  ->  Prims.int = (fun ( x  :  Prims.int ) ( y  :  Prims.int ) -> (x * y))




