// Lean compiler output
// Module: Chap5
// Imports: Init Chap4
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
LEAN_EXPORT lean_object* l_HTPI_plus_x27_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HTPI_square2___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HTPI_plus_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HTPI_square1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_HTPI_square2(lean_object*);
LEAN_EXPORT lean_object* l_HTPI_square1(lean_object*);
LEAN_EXPORT lean_object* l_HTPI_plus_x27_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HTPI_plus(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HTPI_plus___boxed(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HTPI_plus_x27___boxed(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_HTPI_square1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HTPI_square1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HTPI_square1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HTPI_square2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(2u);
x_3 = lean_nat_pow(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HTPI_square2___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_HTPI_square2(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_HTPI_plus(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HTPI_plus___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HTPI_plus(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HTPI_plus_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HTPI_plus_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HTPI_plus_x27(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HTPI_plus_x27_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_int_add(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_HTPI_plus_x27_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_HTPI_plus_x27_x27(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Init(uint8_t builtin, lean_object*);
lean_object* initialize_Chap4(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Chap5(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Chap4(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
