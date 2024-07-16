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
    printf("pupt1\n");
    if (lean_is_scalar(a)) {
        size_t n = lean_unbox(a);
        cout << "n = " << n << flush;
        if (n == 0) {
            lean_internal_panic("prob_UniformP2: n == 0");
        } else {
            int lz = __countl_zero(n);
            int bitlength = (8*sizeof n) - lz - 1;
            cout << " bit length = " << bitlength << "\n" << flush;
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
    cout << "Return\n" << flush;
    //printf("ret\n"); 
    return a;
} 

extern "C" lean_object * prob_Bind(lean_object * f, lean_object * g, lean_object * eta) {
    cout << "Bind\n" << flush;
    //printf("bind\n");
    lean_object * exf = lean_apply_1(f,0);
    //printf(".. 1 \n");
    lean_object * pa = lean_apply_2(g,exf,0);
    //printf(".. 2 \n"); 
    return pa;
} 

extern "C" lean_object * prob_While(lean_object * condition, lean_object * body, lean_object * init, lean_object * eta) {
    cout << "While\n" << flush;
    //printf("while\n");
    lean_object * state = init; 
    //printf(" o condition is ");
    uint8_t cond = lean_unbox(lean_apply_1(condition,state));
    //printf(cond ? "true" : "false");
    while (cond) {
        state = lean_apply_2(body,state,0);
        //printf(" i condition is ");
        cond = lean_unbox(lean_apply_1(condition,state));
        //printf(cond ? "true" : "false");
    }
    //printf("done");
    //cout << " done " << lean_unbox(state) << "\n" << flush;
    return state;
}

extern "C" lean_object * prob_Until(lean_object * body, lean_object * condition, lean_object * eta) {
    printf("pu1\n");
    lean_object * res;
    printf("pu2\n");
    do {
        printf("pu3\n");
        res = lean_apply_1(body,0);
        printf("pu4\n");
    } while (!(lean_unbox(lean_apply_1(condition,res))));
    printf("pu6\n");
    return res;
}

extern "C" lean_object * my_run(lean_object * a) {
    cout << "Run start\n" << flush;
    // if (!rng_initialized) {
    //     //printf("Initializing\n");
    //     struct timeval t1;
    //     gettimeofday(&t1, NULL);
    //     srand(t1.tv_usec * t1.tv_sec);
    //     rng_initialized = 1;
    // }
    lean_object * comp = lean_apply_1(a,0);
    lean_object * res = lean_io_result_mk_ok(comp);
    return res;
} 
