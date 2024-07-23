/**
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights Reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jean-Baptiste Tristan
*/
#include <lean/lean.h>
#include <iostream>
#include <random>

std::random_device generator;

extern "C" lean_object * prob_UniformP2(lean_object * a, lean_object * eta) {
    printf("p2\n");
    lean_dec(eta);
    if (lean_is_scalar(a)) {
        size_t n = lean_unbox(a);
        if (n == 0) {
            lean_internal_panic("prob_UniformP2: n == 0");
        } else {
            int lz = std::__countl_zero(n);
            int bitlength = (8*sizeof n) - lz - 1;
            size_t bound = 1 << bitlength; 
            std::uniform_int_distribution<size_t> distribution(0,bound-1);
            size_t r = distribution(generator);
            lean_dec(a); 
            return lean_box(r);
        }
    } else {
        printf("A\n");
        lean_object * res = lean_usize_to_nat(0);
        printf("B\n");
        do {
            //printf("C\n");
            a = lean_nat_sub(a,lean_box(LEAN_MAX_SMALL_NAT));
            //printf("D\n");
            std::uniform_int_distribution<size_t> distribution(0,LEAN_MAX_SMALL_NAT-1);
            //printf("E\n");
            size_t rdm = distribution(generator);
            //printf("F\n");
            lean_object * acc = lean_usize_to_nat(rdm);
            //printf("G\n");
            res = lean_nat_add(res,acc);
        } while(lean_nat_le(lean_box(LEAN_MAX_SMALL_NAT),a));
        //printf("H\n");
        lean_object * rem = prob_UniformP2(a,lean_box(0));
        printf("I\n");
        return lean_nat_add(res,rem);
        
        // printf("let's go\n");
        // //lean_inc(a);
        // lean_object * d = lean_nat_div(a,lean_box(LEAN_MAX_SMALL_NAT));
        // if (!lean_is_scalar(d)) {
        //     lean_internal_panic("prob_UniformP2: giagantic number, must be an error");
        // }
        // printf("now generate\n");
        // lean_object * res = lean_usize_to_nat(0);
        // for (int i = 0 ; i < lean_unbox(d) ; ++i) {
        //     printf("Loop start\n");
        //     std::uniform_int_distribution<size_t> distribution(0,LEAN_MAX_SMALL_NAT-1);
        //     printf("Loop 1\n");
        //     size_t rdm = distribution(generator);
        //     printf("Loop 2\n");
        //     lean_object * acc = lean_usize_to_nat(rdm);
        //     printf("Loop 3\n");
        //     //lean_inc(res);
        //     //lean_inc(res);
        //     //lean_inc(acc);
        //     printf("Loop 4\n");
        //     res = lean_nat_add(res,acc);
        //     printf("Loop end\n");
        // }
        // printf("done\n");
        // lean_object * r = lean_nat_mod(a,lean_box(LEAN_MAX_SMALL_NAT));
        // lean_object * rem = prob_UniformP2(r,lean_box(0));
        // printf("finished\n");
        // //lean_inc(res);
        // return lean_nat_add(res,rem);
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
