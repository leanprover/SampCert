#include <lean/lean.h>
#include <iostream> 
#include <bit>
#include <chrono>
#include <random>
#include <thread>
#include <mutex>
using namespace std; 

typedef std::chrono::high_resolution_clock myclock;
myclock::time_point beginning = myclock::now();
myclock::duration d = myclock::now() - beginning;
unsigned seed = d.count();
mt19937_64 generator(seed);

//int rng_initialized = 0;
//int seed;

extern "C" lean_object * prob_UniformP2(lean_object * a, lean_object * eta) {
    //printf("pupt1\n");
    if (lean_is_scalar(a)) {
        size_t n = lean_unbox(a);
        //cout << "n = " << n << flush;
        if (n == 0) {
            lean_internal_panic("prob_UniformP2: n == 0");
        } else {
            int lz = __countl_zero(n);
            int bitlength = (8*sizeof n) - lz - 1;
            //cout << " bit length = " << bitlength << "\n" << flush;
            if (bitlength < 30) {
                size_t bound = 1 << bitlength; 
                uniform_int_distribution<int> distribution(0,bound-1);
                size_t r = distribution(generator); // rand() % bound; 
                //cout << " sampled value = " << r << flush; 
                //cout << "\n" << flush;
                //printf("Done\n");
                return lean_box(r);
            } else {
                lean_internal_panic("prob_UniformP2: not handling large values yet");
            }
        }
    } else {
        lean_internal_panic("prob_UniformP2: not handling very large values yet");
    }
}

extern "C" lean_object * prob_Pure(lean_object * a, lean_object * eta) {
    //printf("pr1\n");
    return a;
} 

extern "C" lean_object * prob_Bind(lean_object * f, lean_object * g, lean_object * eta) {
    // if (!(lean_is_closure(f))) {
    //     lean_internal_panic("prob_Bind, f is not a closure");
    // }
    // lean_closure_object * clos_f = lean_to_closure(f);
    // cout << "arity: " << clos_f->m_arity << "\n" << flush;
    // cout << "fixed: " << clos_f->m_num_fixed << "\n" << flush;
    // cout << "arg: " << lean_unbox(clos_f->m_objs[0]) << "\n" << flush;
    // lean_closure_object * inner = lean_to_closure(clos_f->m_objs[1]);
    // cout << "inner_arg: " << lean_unbox(inner->m_objs[0]) << "\n" << flush;

    // if (!(lean_is_closure(g))) {
    //     lean_internal_panic("prob_Bind, g is not a closure");
    // }
    // printf("pb1\n");
    lean_object * exf = lean_apply_1(f,0);
    //printf("pb2\n");
    lean_object * pa = lean_apply_2(g,exf,0);
    //printf("pb3\n");
    return pa;
} 

extern "C" lean_object * prob_While(lean_object * condition, lean_object * body, lean_object * init, lean_object * eta) {
    // if (!(lean_is_closure(body))) {
    //     lean_internal_panic("prob_While, body is not a closure");
    // }
    // lean_closure_object * clos_body = lean_to_closure(body);
    // cout << "arity: " << clos_body->m_arity << "\n" << flush;
    // cout << "fixed: " << clos_body->m_num_fixed << "\n" << flush;
    // if (!(lean_is_closure(condition))) {
    //     lean_internal_panic("prob_While, condition is not a closure");
    // }
    // lean_closure_object * clos_cond = lean_to_closure(condition);
    // cout << "arity: " << clos_cond->m_arity << "\n" << flush;
    // cout << "fixed: " << clos_cond->m_num_fixed << "\n" << flush;
    // printf("pw1\n");
    lean_object * state = init; 
    lean_inc(condition);
    uint8_t cond = lean_unbox(lean_apply_1(condition,state));
    while (cond) {
        lean_inc(body);
        state = lean_apply_2(body,state,0);
        lean_inc(condition);
        cond = lean_unbox(lean_apply_1(condition,state));
    }
    return state;
}

extern "C" lean_object * prob_Until(lean_object * body, lean_object * condition, lean_object * eta) {
    // if (!(lean_is_closure(body))) {
    //     lean_internal_panic("prob_Until, body is not a closure");
    // }
    // lean_closure_object * clos_body = lean_to_closure(body);
    // cout << "arity: " << clos_body->m_arity << "\n" << flush;
    // cout << "fixed: " << clos_body->m_num_fixed << "\n" << flush;
    // cout << "arg: " << lean_unbox(clos_body->m_objs[0]) << "\n" << flush; 
    // if (!(lean_is_closure(condition))) {
    //     lean_internal_panic("prob_Until, condition is not a closure");
    // }
    // lean_closure_object * clos_cond = lean_to_closure(condition);
    // cout << "arity: " << clos_cond->m_arity << "\n" << flush;
    // cout << "fixed: " << clos_cond->m_num_fixed << "\n" << flush;
    // printf("pu1\n");
    lean_object * res;
    //printf("pu2\n");
    do {
        //printf("pu3\n");
        lean_inc(body);
        lean_inc(condition);
        res = lean_apply_1(body,0);
        //printf("pu4\n");
    } while (!(lean_unbox(lean_apply_1(condition,res))));
    //printf("pu6\n");
    return res;
}

extern "C" lean_object * my_run(lean_object * a) {
    // if (!(lean_is_closure(a))) {
    //     lean_internal_panic("my_run, a is not a closure");
    // }
    // cout << "\n\nRun start\n" << flush;
    // lean_closure_object * clos = lean_to_closure(a);
    // cout << "arity: " << clos->m_arity << "\n" << flush;
    // cout << "fixed: " << clos->m_num_fixed << "\n" << flush;
    // cout << "arg: " << lean_unbox(clos->m_objs[0]) << "\n" << flush;
    // if (!rng_initialized) {
    //     //printf("Initializing\n");
    //     struct timeval t1;
    //     gettimeofday(&t1, NULL);
    //     srand(t1.tv_usec * t1.tv_sec);
    //     rng_initialized = 1;
    // }
    //printf("mr1\n");
    lean_object * comp = lean_apply_1(a,0);
    //printf("mr2\n");
    lean_object * res = lean_io_result_mk_ok(comp);
    //printf("mr3\n");
    return res;
} 
