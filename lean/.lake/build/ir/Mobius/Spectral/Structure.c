// Lean compiler output
// Module: Mobius.Spectral.Structure
// Imports: public import Init public meta import Init public import Mobius.Spectral.Basic public import Mathlib.Algebra.Ring.GeomSum public import Mathlib.Data.Int.GCD public import Mathlib.Tactic.LinearCombination public import Mathlib.Tactic.GCongr
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
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Init(uint8_t builtin);
lean_object* initialize_Mobius_Mobius_Spectral_Basic(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Algebra_Ring_GeomSum(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Data_Int_GCD(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_LinearCombination(uint8_t builtin);
lean_object* initialize_mathlib_Mathlib_Tactic_GCongr(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Mobius_Mobius_Spectral_Structure(uint8_t builtin) {
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
res = initialize_mathlib_Mathlib_Algebra_Ring_GeomSum(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Data_Int_GCD(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_LinearCombination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_mathlib_Mathlib_Tactic_GCongr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
