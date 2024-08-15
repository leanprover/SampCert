/**
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
*/
#include <lean/lean.h>
#include <fcntl.h>
#include <unistd.h>
#include <random>

static int urandom = -1; 

extern "C" lean_object * prob_UniformByte (lean_object * eta) {
    lean_dec(eta);
    unsigned char r;
    read(urandom, &r,1);
    return lean_box((size_t) r);
}

extern "C" lean_object * prob_Pure(lean_object * a, lean_object * eta) {
    lean_dec(eta);
    return a;
} 

extern "C" lean_object * prob_Bind(lean_object * f, lean_object * g, lean_object * eta) {
    lean_dec(eta);
    lean_object * exf = lean_apply_1(f,lean_box(0));
    lean_object * pa = lean_apply_2(g,exf,lean_box(0));
    return pa;
} 

extern "C" lean_object * prob_While(lean_object * condition, lean_object * body, lean_object * init, lean_object * eta) {
    lean_dec(eta);
    lean_object * state = init; 
    lean_inc(state);
    lean_inc(condition);
    uint8_t cond = lean_unbox(lean_apply_1(condition,state));
    while (cond) {
        lean_inc(body);
        state = lean_apply_2(body,state,lean_box(0));
        lean_inc(condition);
        lean_inc(state);
        cond = lean_unbox(lean_apply_1(condition,state));
    }
    return state;
}

extern "C" lean_object * my_run(lean_object * a) {
    if (urandom == -1) {
        urandom = open("/dev/urandom", O_RDONLY | O_CLOEXEC);
        if (urandom == -1) {
            lean_internal_panic("prob_UniformByte: /dev/urandom cannot be opened");
        }
    }
    lean_object * comp = lean_apply_1(a,lean_box(0));
    lean_object * res = lean_io_result_mk_ok(comp);
    return res;
} 

extern "C" uint32_t dirty_io_get(lean_object * a) {
    lean_object * r1 = lean_apply_1(a,lean_box(0));
    lean_object * r2 = lean_io_result_get_value(r1);
    if (lean_is_scalar(r2)) {
        size_t r3 = lean_unbox(r2);
        return r3;
    } else {
        lean_internal_panic("dirty_io_get: value not scalar");
    }
}
