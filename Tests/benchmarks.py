#!/usr/bin/env python3

# Benchmarking the discrete Gaussian sampler

import SampCert
import matplotlib.pyplot as plt
import timeit
import secrets
import numpy as np
from datetime import datetime
import tqdm as tqdm
from decimal import Decimal
import argparse

from diffprivlib.mechanisms.base import bernoulli_neg_exp
from diffprivlib.mechanisms import GaussianDiscrete

from fractions import Fraction
from discretegauss import sample_dlaplace, sample_dgauss

sampler = SampCert.SLang()
rng = secrets.SystemRandom()

def gaussian_benchmarks(mix, warmup_attempts, measured_attempts, lb ,ub, quantity):
    # Values of epsilon attempted
    sigmas = []

    g = GaussianDiscrete(epsilon=0.01, delta=0.00001)


    # SampCert
    means = []
    stdevs = []
    for i in mix:
        means.append([])
        stdevs.append([])

    # sample_dgauss
    ibm_dg_mean = []
    ibm_dg_stdev = []

    # DiffPrivLib GaussianDiscrete
    ibm_dpl_mean = []
    ibm_dpl_stdev = []

    num_attempts = warmup_attempts + measured_attempts

    for sigma in tqdm.tqdm(np.linspace(lb+0.001,ub,quantity)):
        
        g._scale = sigma
        sigmas += [sigma]

        sigma_num, sigma_denom = Decimal(sigma).as_integer_ratio()
        sigma_squared = sigma ** 2

        times = []
        for i in mix:
            times.append([])        

        t_ibm_dg = []
        t_ibm_dpl = []
         
        for m in range(len(mix)): 
            for i in range(num_attempts):
                start_time = timeit.default_timer()
                sampler.DiscreteGaussianSample(sigma_num, sigma_denom, mix[m])
                elapsed = timeit.default_timer() - start_time
                times[m].append(elapsed)

        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sample_dgauss(sigma_squared, rng)
            elapsed = timeit.default_timer() - start_time
            t_ibm_dg.append(elapsed)

        for i in range(num_attempts):
            start_time = timeit.default_timer()
            g.randomise(0)
            elapsed = timeit.default_timer() - start_time
            t_ibm_dpl.append(elapsed)

        measured = []
        # Compute mean and stdev
        for m in range(len(mix)): 
            measured.append(np.array(times[m][-measured_attempts:]))
        ibm_dg_measured = np.array(t_ibm_dg[-measured_attempts:])
        ibm_dpl_measured = np.array(t_ibm_dpl[-measured_attempts:])

        # Convert s to ms
        for m in range(len(mix)): 
            means[m].append(measured[m].mean() * 1000.0)
            stdevs[m].append(measured[m].std() * 1000.0)
        ibm_dg_mean.append(ibm_dg_measured.mean() * 1000.0)
        ibm_dg_stdev.append(ibm_dg_measured.std() * 1000.0)
        ibm_dpl_mean.append(ibm_dpl_measured.mean() * 1000.0)
        ibm_dpl_stdev.append(ibm_dpl_measured.std() * 1000.0)


    fig,ax1 = plt.subplots()

    color = plt.cm.rainbow(np.linspace(0, 1, len(mix) + 2))

    for m in range(len(mix)): 
        ax1.plot(sigmas, means[m], color=color[2 + m], linewidth=1.0, label='DiscreteGaussianSample' + ' mix = ' + str(mix[m]))
        ax1.fill_between(sigmas, np.array(means[m])-0.5*np.array(stdevs[m]), np.array(means[m])+0.5*np.array(stdevs[m]),
                        alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)

    ax1.plot(sigmas, ibm_dg_mean, color=color[0], linewidth=1.0, label='IBM sample_dgauss')
    ax1.fill_between(sigmas, np.array(ibm_dg_mean)-0.5*np.array(ibm_dg_stdev), np.array(ibm_dg_mean)+0.5*np.array(ibm_dg_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)

    ax1.plot(sigmas, ibm_dpl_mean, color=color[1], linewidth=1.0, label='IBM diffprivlib')
    ax1.fill_between(sigmas, np.array(ibm_dpl_mean)-0.5*np.array(ibm_dpl_stdev), np.array(ibm_dpl_mean)+0.5*np.array(ibm_dpl_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)

    ax1.set_xlabel("Sigma")
    ax1.set_ylabel("Sampling Time (ms)")
    plt.legend(loc = 'best')
    now = datetime.now()
    filename = 'GaussianBenchmarks' + now.strftime("%H%M%S") + '.pdf'
    plt.savefig(filename)

if __name__ == "__main__":

    parser = argparse.ArgumentParser()
    parser.add_argument("--mix", nargs="+", type=int, help="mix", default=[0])
    parser.add_argument("--warmup", type=int, help="warmup", default=0)
    parser.add_argument("--trials", type=int, help="trials", default=1000)
    parser.add_argument("--min", type=int, help="min", default=1)
    parser.add_argument("--max", type=int, help="max", default=500)
    parser.add_argument("--quantity", type=int, help="step", default=10)
    args = parser.parse_args()

    gaussian_benchmarks(args.mix,args.warmup,args.trials,args.min,args.max,args.quantity)
