// Lean compiler output
// Module: Mobius.Spectral.Modulation
// Imports: public import Init public meta import Init public import Mobius.Spectral.Basic
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
lean_object* lp_mathlib_Field_toSemifield___redArg(lean_object*);
lean_object* lp_mathlib_Semifield_toDivisionSemiring___redArg(lean_object*);
lean_object* lp_mathlib_instDistribOfSemiring___redArg(lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_modul___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_modul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_modul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lp_Mobius_Mobius_modul___redArg___lam__0(lean_object* v_inst_1_, lean_object* v_00_u03b6_2_, lean_object* v_toMul_3_, lean_object* v_u_4_, lean_object* v_n_5_){
_start:
{
lean_object* v_zpow_6_; lean_object* v___x_7_; lean_object* v___x_8_; lean_object* v___x_9_; 
v_zpow_6_ = lean_ctor_get(v_inst_1_, 3);
lean_inc(v_zpow_6_);
lean_dec_ref(v_inst_1_);
lean_inc(v_n_5_);
v___x_7_ = lean_apply_2(v_zpow_6_, v_n_5_, v_00_u03b6_2_);
v___x_8_ = lean_apply_1(v_u_4_, v_n_5_);
v___x_9_ = lean_apply_2(v_toMul_3_, v___x_7_, v___x_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_modul___redArg(lean_object* v_inst_10_, lean_object* v_00_u03b6_11_){
_start:
{
lean_object* v___x_12_; lean_object* v___x_13_; lean_object* v_toSemiring_14_; lean_object* v___x_15_; lean_object* v_toMul_16_; lean_object* v___f_17_; 
v___x_12_ = lp_mathlib_Field_toSemifield___redArg(v_inst_10_);
v___x_13_ = lp_mathlib_Semifield_toDivisionSemiring___redArg(v___x_12_);
v_toSemiring_14_ = lean_ctor_get(v___x_13_, 0);
lean_inc_ref(v_toSemiring_14_);
lean_dec_ref(v___x_13_);
v___x_15_ = lp_mathlib_instDistribOfSemiring___redArg(v_toSemiring_14_);
v_toMul_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc(v_toMul_16_);
lean_dec_ref(v___x_15_);
v___f_17_ = lean_alloc_closure((void*)(lp_Mobius_Mobius_modul___redArg___lam__0), 5, 3);
lean_closure_set(v___f_17_, 0, v_inst_10_);
lean_closure_set(v___f_17_, 1, v_00_u03b6_11_);
lean_closure_set(v___f_17_, 2, v_toMul_16_);
return v___f_17_;
}
}
LEAN_EXPORT lean_object* lp_Mobius_Mobius_modul(lean_object* v_k_18_, lean_object* v_inst_19_, lean_object* v_00_u03b6_20_){
_start:
{
lean_object* v___x_21_; 
v___x_21_ = lp_Mobius_Mobius_modul___redArg(v_inst_19_, v_00_u03b6_20_);
return v___x_21_;
}
}
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mobius_Mobius_Spectral_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mobius_Mobius_Spectral_Modulation(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Mobius_Mobius_Spectral_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
