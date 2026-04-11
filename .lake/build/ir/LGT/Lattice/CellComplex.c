// Lean compiler output
// Module: LGT.Lattice.CellComplex
// Imports: public import Init public import Lattice.Sites public import Torus.AsymmetricTorus
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
uint8_t lp_mathlib_ZMod_decidableEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticeLink_decEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticeLink_decEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_finRange(lean_object*);
uint8_t lp_mathlib_Fintype_decidablePiFintype___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticeLink_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticeLink_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticeLink(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticeLink___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lp_mathlib_ZMod_commRing(lean_object*);
lean_object* lp_mathlib_CommRing_toNonUnitalCommRing___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(lean_object*);
lean_object* lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(lean_object*);
lean_object* lp_mathlib_Ring_toAddGroupWithOne___redArg(lean_object*);
lean_object* lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_siteShift___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_siteShift(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_siteShift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_LatticeLink_target___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_LatticeLink_target(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_LatticeLink_target___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticePlaquette_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticePlaquette_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticePlaquette(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticePlaquette___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_LatticePlaquette_boundaryLinks(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_LatticePlaquette_boundaryLinks___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorElim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorElim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorElim(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_time_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_time_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_time_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_time_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_space_elim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_space_elim___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_space_elim(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_space_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_Dir2D_ofNat(lean_object*);
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ofNat___boxed(lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqDir2D(uint8_t, uint8_t);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqDir2D___boxed(lean_object*, lean_object*);
static lean_once_cell_t lp_LGT_Dir2D_enumList___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LGT_Dir2D_enumList___closed__0;
static lean_once_cell_t lp_LGT_Dir2D_enumList___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LGT_Dir2D_enumList___closed__1;
LEAN_EXPORT lean_object* lp_LGT_Dir2D_enumList;
LEAN_EXPORT lean_object* lp_LGT_instFintypeDir2D;
static const lean_string_object lp_LGT_instReprDir2D_repr___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Dir2D.time"};
static const lean_object* lp_LGT_instReprDir2D_repr___closed__0 = (const lean_object*)&lp_LGT_instReprDir2D_repr___closed__0_value;
static const lean_ctor_object lp_LGT_instReprDir2D_repr___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LGT_instReprDir2D_repr___closed__0_value)}};
static const lean_object* lp_LGT_instReprDir2D_repr___closed__1 = (const lean_object*)&lp_LGT_instReprDir2D_repr___closed__1_value;
static const lean_string_object lp_LGT_instReprDir2D_repr___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Dir2D.space"};
static const lean_object* lp_LGT_instReprDir2D_repr___closed__2 = (const lean_object*)&lp_LGT_instReprDir2D_repr___closed__2_value;
static const lean_ctor_object lp_LGT_instReprDir2D_repr___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&lp_LGT_instReprDir2D_repr___closed__2_value)}};
static const lean_object* lp_LGT_instReprDir2D_repr___closed__3 = (const lean_object*)&lp_LGT_instReprDir2D_repr___closed__3_value;
lean_object* lean_nat_to_int(lean_object*);
static lean_once_cell_t lp_LGT_instReprDir2D_repr___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LGT_instReprDir2D_repr___closed__4;
static lean_once_cell_t lp_LGT_instReprDir2D_repr___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_LGT_instReprDir2D_repr___closed__5;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instReprDir2D_repr(uint8_t, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instReprDir2D_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_LGT_instReprDir2D___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_LGT_instReprDir2D_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_LGT_instReprDir2D___closed__0 = (const lean_object*)&lp_LGT_instReprDir2D___closed__0_value;
LEAN_EXPORT const lean_object* lp_LGT_instReprDir2D = (const lean_object*)&lp_LGT_instReprDir2D___closed__0_value;
lean_object* lp_mathlib_ZMod_decidableEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqAsymLink_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqAsymLink_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqAsymLink(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqAsymLink___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_AsymLink_target(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqAsymPlaquette_decEq(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqAsymPlaquette_decEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqAsymPlaquette(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqAsymPlaquette___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_AsymPlaquette_boundaryLinks(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_LGT_AsymPlaquette_boundaryLinks___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticeLink_decEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_mathlib_ZMod_decidableEq(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticeLink_decEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqLatticeLink_decEq___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticeLink_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_4, 1);
lean_inc(x_8);
lean_dec_ref(x_4);
x_9 = lean_alloc_closure((void*)(lp_LGT_instDecidableEqLatticeLink_decEq___lam__0___boxed), 4, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = l_List_finRange(x_1);
x_11 = lp_mathlib_Fintype_decidablePiFintype___redArg(x_9, x_10, x_5, x_7);
if (x_11 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_eq(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticeLink_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqLatticeLink_decEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticeLink(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_LGT_instDecidableEqLatticeLink_decEq(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticeLink___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqLatticeLink(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_LGT_siteShift___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lp_mathlib_ZMod_commRing(x_1);
lean_inc_ref(x_5);
x_6 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_5);
x_7 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_6);
x_8 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_5);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec_ref(x_11);
lean_inc(x_2);
lean_inc(x_3);
x_13 = lean_apply_1(x_2, x_3);
x_14 = lean_apply_2(x_9, x_13, x_12);
x_15 = lp_mathlib_Function_update___at___00OrderedFinpartition_extendMiddle_spec__0___redArg(x_2, x_3, x_14, x_4);
lean_dec(x_14);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* lp_LGT_siteShift(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_LGT_siteShift___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_LGT_siteShift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lp_LGT_siteShift(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_LGT_LatticeLink_target___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lp_LGT_siteShift___redArg(x_1, x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_LGT_LatticeLink_target(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_LGT_LatticeLink_target___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_LatticeLink_target___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_LGT_LatticeLink_target(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticePlaquette_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_3, 2);
lean_inc(x_7);
lean_dec_ref(x_3);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
lean_dec_ref(x_4);
x_11 = lean_alloc_closure((void*)(lp_LGT_instDecidableEqLatticeLink_decEq___lam__0___boxed), 4, 1);
lean_closure_set(x_11, 0, x_2);
x_12 = l_List_finRange(x_1);
x_13 = lp_mathlib_Fintype_decidablePiFintype___redArg(x_11, x_12, x_5, x_8);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (x_14 == 0)
{
lean_dec(x_10);
lean_dec(x_7);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_7, x_10);
lean_dec(x_10);
lean_dec(x_7);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticePlaquette_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqLatticePlaquette_decEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqLatticePlaquette(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_LGT_instDecidableEqLatticePlaquette_decEq(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqLatticePlaquette___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqLatticePlaquette(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_LGT_LatticePlaquette_boundaryLinks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_eq(x_4, x_5);
if (x_6 == 1)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec_ref(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_4, x_10);
x_12 = lean_nat_dec_eq(x_11, x_5);
if (x_12 == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 2);
lean_inc(x_15);
lean_dec_ref(x_3);
x_16 = lean_alloc_closure((void*)(lp_LGT_siteShift___boxed), 5, 4);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_13);
lean_closure_set(x_16, 3, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_nat_sub(x_11, x_10);
lean_dec(x_11);
x_19 = lean_nat_dec_eq(x_18, x_5);
if (x_19 == 1)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 2);
lean_inc(x_22);
lean_dec_ref(x_3);
x_23 = lean_alloc_closure((void*)(lp_LGT_siteShift___boxed), 5, 4);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_2);
lean_closure_set(x_23, 2, x_20);
lean_closure_set(x_23, 3, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
return x_24;
}
else
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_nat_sub(x_18, x_10);
lean_dec(x_18);
x_26 = lean_nat_dec_eq(x_25, x_5);
lean_dec(x_25);
x_27 = lean_ctor_get(x_3, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
lean_dec_ref(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_LGT_LatticePlaquette_boundaryLinks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_LGT_LatticePlaquette_boundaryLinks(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_LGT_Dir2D_ctorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_toCtorIdx(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_LGT_Dir2D_ctorIdx(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
x_3 = lp_LGT_Dir2D_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorElim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorElim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_LGT_Dir2D_ctorElim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorElim(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_inc(x_5);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
x_7 = lp_LGT_Dir2D_ctorElim(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_time_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_time_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_LGT_Dir2D_time_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_time_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_time_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_LGT_Dir2D_time_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_space_elim___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_space_elim___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lp_LGT_Dir2D_space_elim___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_space_elim(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_inc(x_4);
return x_4;
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_space_elim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
x_6 = lp_LGT_Dir2D_space_elim(x_1, x_5, x_3, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_LGT_Dir2D_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_le(x_1, x_2);
if (x_3 == 0)
{
uint8_t x_4; 
x_4 = 1;
return x_4;
}
else
{
uint8_t x_5; 
x_5 = 0;
return x_5;
}
}
}
LEAN_EXPORT lean_object* lp_LGT_Dir2D_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lp_LGT_Dir2D_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqDir2D(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lp_LGT_Dir2D_ctorIdx(x_1);
x_4 = lp_LGT_Dir2D_ctorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqDir2D___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
x_4 = lean_unbox(x_2);
x_5 = lp_LGT_instDecidableEqDir2D(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_lp_LGT_Dir2D_enumList___closed__0(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(0);
x_2 = 1;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_LGT_Dir2D_enumList___closed__1(void) {
_start:
{
lean_object* x_1; uint8_t x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_obj_once(&lp_LGT_Dir2D_enumList___closed__0, &lp_LGT_Dir2D_enumList___closed__0_once, _init_lp_LGT_Dir2D_enumList___closed__0);
x_2 = 0;
x_3 = lean_box(x_2);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
static lean_object* _init_lp_LGT_Dir2D_enumList(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&lp_LGT_Dir2D_enumList___closed__1, &lp_LGT_Dir2D_enumList___closed__1_once, _init_lp_LGT_Dir2D_enumList___closed__1);
return x_1;
}
}
static lean_object* _init_lp_LGT_instFintypeDir2D(void) {
_start:
{
lean_object* x_1; 
x_1 = lp_LGT_Dir2D_enumList;
return x_1;
}
}
static lean_object* _init_lp_LGT_instReprDir2D_repr___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(2u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
static lean_object* _init_lp_LGT_instReprDir2D_repr___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_nat_to_int(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lp_LGT_instReprDir2D_repr(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_10; 
if (x_1 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1024u);
x_18 = lean_nat_dec_le(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_obj_once(&lp_LGT_instReprDir2D_repr___closed__4, &lp_LGT_instReprDir2D_repr___closed__4_once, _init_lp_LGT_instReprDir2D_repr___closed__4);
x_3 = x_19;
goto block_9;
}
else
{
lean_object* x_20; 
x_20 = lean_obj_once(&lp_LGT_instReprDir2D_repr___closed__5, &lp_LGT_instReprDir2D_repr___closed__5_once, _init_lp_LGT_instReprDir2D_repr___closed__5);
x_3 = x_20;
goto block_9;
}
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_obj_once(&lp_LGT_instReprDir2D_repr___closed__4, &lp_LGT_instReprDir2D_repr___closed__4_once, _init_lp_LGT_instReprDir2D_repr___closed__4);
x_10 = x_23;
goto block_16;
}
else
{
lean_object* x_24; 
x_24 = lean_obj_once(&lp_LGT_instReprDir2D_repr___closed__5, &lp_LGT_instReprDir2D_repr___closed__5_once, _init_lp_LGT_instReprDir2D_repr___closed__5);
x_10 = x_24;
goto block_16;
}
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = ((lean_object*)(lp_LGT_instReprDir2D_repr___closed__1));
x_5 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = 0;
x_7 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = ((lean_object*)(lp_LGT_instReprDir2D_repr___closed__3));
x_12 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = 0;
x_14 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set_uint8(x_14, sizeof(void*)*1, x_13);
x_15 = l_Repr_addAppParen(x_14, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* lp_LGT_instReprDir2D_repr___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
x_4 = lp_LGT_instReprDir2D_repr(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqAsymLink_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
lean_dec_ref(x_3);
x_7 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_7);
x_8 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
lean_dec_ref(x_4);
x_9 = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_instDecidableEqProd___redArg(x_9, x_10, x_5, x_7);
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lp_LGT_instDecidableEqDir2D(x_6, x_8);
return x_12;
}
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqAsymLink_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqAsymLink_decEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqAsymLink(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_LGT_instDecidableEqAsymLink_decEq(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqAsymLink___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqAsymLink(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_LGT_AsymLink_target(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_4 = lp_mathlib_ZMod_commRing(x_1);
lean_inc_ref(x_4);
x_5 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_4);
x_6 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_5);
x_7 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_6);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_4);
x_10 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 2);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lp_mathlib_ZMod_commRing(x_2);
lean_inc_ref(x_12);
x_13 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_12);
x_14 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_13);
x_15 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_14);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_12);
x_18 = lean_ctor_get(x_17, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_17);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*1);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
lean_dec_ref(x_18);
lean_dec(x_16);
x_20 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_20);
lean_dec_ref(x_3);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_apply_2(x_8, x_22, x_11);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_apply_2(x_8, x_24, x_11);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_dec(x_11);
lean_dec(x_8);
x_28 = lean_ctor_get(x_3, 0);
lean_inc_ref(x_28);
lean_dec_ref(x_3);
x_29 = lean_ctor_get(x_18, 2);
lean_inc(x_29);
lean_dec_ref(x_18);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_apply_2(x_16, x_31, x_29);
lean_ctor_set(x_28, 1, x_32);
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_apply_2(x_16, x_34, x_29);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqAsymPlaquette_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = lean_alloc_closure((void*)(lp_mathlib_ZMod_decidableEq___boxed), 3, 1);
lean_closure_set(x_6, 0, x_2);
x_7 = l_instDecidableEqProd___redArg(x_5, x_6, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqAsymPlaquette_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqAsymPlaquette_decEq(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t lp_LGT_instDecidableEqAsymPlaquette(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lp_LGT_instDecidableEqAsymPlaquette_decEq(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* lp_LGT_instDecidableEqAsymPlaquette___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lp_LGT_instDecidableEqAsymPlaquette(x_1, x_2, x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* lp_LGT_AsymPlaquette_boundaryLinks(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_5 = lp_mathlib_ZMod_commRing(x_1);
lean_inc_ref(x_5);
x_6 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_5);
x_7 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_6);
x_8 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_7);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec_ref(x_8);
x_10 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_5);
x_11 = lean_ctor_get(x_10, 1);
lean_inc_ref(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lp_mathlib_ZMod_commRing(x_2);
lean_inc_ref(x_13);
x_14 = lp_mathlib_CommRing_toNonUnitalCommRing___redArg(x_13);
x_15 = lp_mathlib_NonUnitalNonAssocRing_toNonUnitalNonAssocSemiring___redArg(x_14);
x_16 = lp_mathlib_NonUnitalNonAssocSemiring_toDistrib___redArg(x_15);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lp_mathlib_Ring_toAddGroupWithOne___redArg(x_13);
x_19 = lean_ctor_get(x_18, 1);
lean_inc_ref(x_19);
lean_dec_ref(x_18);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_4, x_21);
if (x_22 == 1)
{
uint8_t x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_9);
x_23 = 0;
x_24 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set_uint8(x_24, sizeof(void*)*1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_sub(x_4, x_25);
x_27 = lean_nat_dec_eq(x_26, x_21);
if (x_27 == 1)
{
uint8_t x_28; 
lean_dec(x_26);
lean_dec(x_20);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_3);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_3, 0);
x_30 = lean_apply_2(x_9, x_29, x_12);
lean_ctor_set(x_3, 0, x_30);
x_31 = 1;
x_32 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_31);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_3, 0);
x_34 = lean_ctor_get(x_3, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_3);
x_35 = lean_apply_2(x_9, x_33, x_12);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = 1;
x_38 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set_uint8(x_38, sizeof(void*)*1, x_37);
return x_38;
}
}
else
{
lean_object* x_39; uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_9);
x_39 = lean_nat_sub(x_26, x_25);
lean_dec(x_26);
x_40 = lean_nat_dec_eq(x_39, x_21);
if (x_40 == 1)
{
uint8_t x_41; 
lean_dec(x_39);
x_41 = !lean_is_exclusive(x_3);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_3, 1);
x_43 = lean_apply_2(x_17, x_42, x_20);
lean_ctor_set(x_3, 1, x_43);
x_44 = 0;
x_45 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_45, 0, x_3);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_44);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_3, 0);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_3);
x_48 = lean_apply_2(x_17, x_47, x_20);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = 0;
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_50);
return x_51;
}
}
else
{
lean_object* x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; 
lean_dec(x_20);
lean_dec(x_17);
x_52 = lean_nat_sub(x_39, x_25);
lean_dec(x_39);
x_53 = lean_nat_dec_eq(x_52, x_21);
lean_dec(x_52);
x_54 = 1;
x_55 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_55, 0, x_3);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_54);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* lp_LGT_AsymPlaquette_boundaryLinks___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lp_LGT_AsymPlaquette_boundaryLinks(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_GaussianField_Lattice_Sites(uint8_t builtin);
lean_object* initialize_GaussianField_Torus_AsymmetricTorus(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_LGT_LGT_Lattice_CellComplex(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GaussianField_Lattice_Sites(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_GaussianField_Torus_AsymmetricTorus(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
lp_LGT_Dir2D_enumList = _init_lp_LGT_Dir2D_enumList();
lean_mark_persistent(lp_LGT_Dir2D_enumList);
lp_LGT_instFintypeDir2D = _init_lp_LGT_instFintypeDir2D();
lean_mark_persistent(lp_LGT_instFintypeDir2D);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
