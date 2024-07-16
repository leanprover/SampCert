/**
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
*/
#include <lean/lean.h>
#include <iostream> 
#include <bit>
#include <chrono>
#include <random>
using namespace std; 

typedef std::chrono::high_resolution_clock myclock;
myclock::time_point beginning = myclock::now();
myclock::duration d = myclock::now() - beginning;
unsigned seed = d.count();
mt19937_64 generator(seed);

extern "C" lean_object * prob_UniformP2(lean_object * a, lean_object * eta) {
    lean_dec(eta);
    if (lean_is_scalar(a)) {
        size_t n = lean_unbox(a);
        if (n == 0) {
            lean_internal_panic("prob_UniformP2: n == 0");
        } else {
            int lz = __countl_zero(n);
            int bitlength = (8*sizeof n) - lz - 1;
            size_t bound = 1 << bitlength; 
            uniform_int_distribution<int> distribution(0,bound-1);
            size_t r = distribution(generator);
            lean_dec(a); 
            return lean_box(r);
        }
    } else {
        lean_internal_panic("prob_UniformP2: not handling very large values yet");
    }
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
    lean_object * comp = lean_apply_1(a,lean_box(0));
    lean_object * res = lean_io_result_mk_ok(comp);
    return res;
} 
