// Lean compiler output
// Module: Mobius.Basic
// Imports: public import Init public meta import Init public import Mathlib.LinearAlgebra.Eigenspace.Basic public import Mathlib.Algebra.CharP.Lemmas public import Mathlib.Algebra.Polynomial.AlgebraMap public import Mathlib.Algebra.Module.Torsion.Field
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
static lean_once_cell_t lp_Mobius_Mobius_shift___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* lp_Mobius_Mobius_shift___lam__0___closed__0;
LEAN_EXPORT lean_object* lp_Mobius_Mobius_shift___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_shift___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object lp_Mobius_Mobius_shift___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)lp_Mobius_Mobius_shift___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* lp_Mobius_Mobius_shift___closed__0 = (const lean_object*)&lp_Mobius_Mobius_shift___closed__0_value;
LEAN_EXPORT lean_object* lp_Mobius_Mobius_shift(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_shift___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_lp_Mobius_Mobius_shift___lam__0___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; 
v___x_1_ = lean_unsigned_to_nat(1u);
v___x_2_ = lean_nat_to_int(v___x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_shift___lam__0(lean_object* v_u_3_, lean_object* v_n_4_){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v___x_5_ = lean_obj_once(&lp_Mobius_Mobius_shift___lam__0___closed__0, &lp_Mobius_Mobius_shift___lam__0___closed__0_once, _init_lp_Mobius_Mobius_shift___lam__0___closed__0);
v___x_6_ = lean_int_add(v_n_4_, v___x_5_);
v___x_7_ = lean_apply_1(v_u_3_, v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_shift___lam__0___boxed(lean_object* v_u_8_, lean_object* v_n_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = lp_Mobius_Mobius_shift___lam__0(v_u_8_, v_n_9_);
lean_dec(v_n_9_);
return v_res_10_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_shift(lean_object* v_k_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = ((lean_object*)(lp_Mobius_Mobius_shift___closed__0));
return v___f_14_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_shift___boxed(lean_object* v_k_15_, lean_object* v_inst_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = lp_Mobius_Mobius_shift(v_k_15_, v_inst_16_);
lean_dec_ref(v_inst_16_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim___redArg___lam__0(lean_object* v_d_18_, lean_object* v_u_19_, lean_object* v_n_20_){
_start:
{
lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_21_ = lean_nat_to_int(v_d_18_);
v___x_22_ = lean_int_mul(v___x_21_, v_n_20_);
lean_dec(v___x_21_);
v___x_23_ = lean_apply_1(v_u_19_, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim___redArg___lam__0___boxed(lean_object* v_d_24_, lean_object* v_u_25_, lean_object* v_n_26_){
_start:
{
lean_object* v_res_27_; 
v_res_27_ = lp_Mobius_Mobius_decim___redArg___lam__0(v_d_24_, v_u_25_, v_n_26_);
lean_dec(v_n_26_);
return v_res_27_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim___redArg(lean_object* v_d_28_){
_start:
{
lean_object* v___f_29_; 
v___f_29_ = lean_alloc_closure((void*)(lp_Mobius_Mobius_decim___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_29_, 0, v_d_28_);
return v___f_29_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim(lean_object* v_k_30_, lean_object* v_inst_31_, lean_object* v_d_32_){
_start:
{
lean_object* v___f_33_; 
v___f_33_ = lean_alloc_closure((void*)(lp_Mobius_Mobius_decim___redArg___lam__0___boxed), 3, 1);
lean_closure_set(v___f_33_, 0, v_d_32_);
return v___f_33_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_decim___boxed(lean_object* v_k_34_, lean_object* v_inst_35_, lean_object* v_d_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = lp_Mobius_Mobius_decim(v_k_34_, v_inst_35_, v_d_36_);
lean_dec_ref(v_inst_35_);
return v_res_37_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_LinearAlgebra_Eigenspace_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_CharP_Lemmas(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Polynomial_AlgebraMap(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Module_Torsion_Field(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mobius_Mobius_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_LinearAlgebra_Eigenspace_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_CharP_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Polynomial_AlgebraMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Algebra_Module_Torsion_Field(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
