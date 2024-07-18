#!/usr/bin/env python3

# Benchmarking the implementations of DiscreteLaplaceSample and DiscreteLaplaceSample'
# Based on the benchmarks in Dafny-VMC

import SampCert
import matplotlib.pyplot as plt
import timeit
import secrets
import numpy
from datetime import datetime
import tqdm as tqdm
from decimal import Decimal

from diffprivlib.mechanisms.base import bernoulli_neg_exp
from diffprivlib.mechanisms import GaussianDiscrete

# source: https://github.com/IBM/discrete-gaussian-differential-privacy
from fractions import Fraction
from discretegauss import sample_dlaplace, sample_dgauss

sampler = SampCert.SLang()
rng = secrets.SystemRandom()

def gaussian_benchmarks():
    print("=========================================================================\n\
Benchmark: Discrete Gaussians \n\
=========================================================================")
    # Values of epsilon attempted
    sigmas = []

    # SampCert DiscreteGaussianSample
    dg_mean = []
    dg_stdev = []

    # IBM sample_dgauss
    ibm_dg_mean = []
    ibm_dg_stdev = []

    # IBM DiffPrivLib GaussianDiscrete
    ibm_dpl_mean = []
    ibm_dpl_stdev = []

    # Benchmark Parameters
    warmup_attempts = 100
    measured_attempts = 2000
    num_attempts = warmup_attempts + measured_attempts

    for epsilon_times_100 in tqdm.tqdm(range(1, 500, 2)):
        g = GaussianDiscrete(epsilon=0.01 * epsilon_times_100, delta=0.00001)
        sigma = g._scale
        sigmas += [sigma]

        sigma_num, sigma_denom = Decimal(sigma).as_integer_ratio()
        sigma_squared = sigma ** 2

        t_dg = []
        t_ibm_dg = []
        t_ibm_dpl = []

        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sampler.DiscreteGaussianSample(sigma_num, sigma_denom)
            elapsed = timeit.default_timer() - start_time
            t_dg.append(elapsed)

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

        # Compute mean and stdev
        dg_measured = numpy.array(t_dg[-measured_attempts:])
        ibm_dg_measured = numpy.array(t_ibm_dg[-measured_attempts:])
        ibm_dpl_measured = numpy.array(t_ibm_dpl[-measured_attempts:])

        # Convert s to ms
        dg_mean.append(dg_measured.mean() * 1000.0)
        dg_stdev.append(dg_measured.std() * 1000.0)
        ibm_dg_mean.append(ibm_dg_measured.mean() * 1000.0)
        ibm_dg_stdev.append(ibm_dg_measured.std() * 1000.0)
        ibm_dpl_mean.append(ibm_dpl_measured.mean() * 1000.0)
        ibm_dpl_stdev.append(ibm_dpl_measured.std() * 1000.0)


    fig,ax1 = plt.subplots()

    ax1.plot(sigmas, dg_mean, color='red', linewidth=1.0, label='DiscreteGaussianSample')
    ax1.fill_between(sigmas, numpy.array(dg_mean)-0.5*numpy.array(dg_stdev), numpy.array(dg_mean)+0.5*numpy.array(dg_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)

    ax1.plot(sigmas, ibm_dg_mean, color='blue', linewidth=1.0, label='IBM sample_dgauss')
    ax1.fill_between(sigmas, numpy.array(ibm_dg_mean)-0.5*numpy.array(ibm_dg_stdev), numpy.array(ibm_dg_mean)+0.5*numpy.array(ibm_dg_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)

    ax1.plot(sigmas, ibm_dpl_mean, color='green', linewidth=1.0, label='IBM diffprivlib')
    ax1.fill_between(sigmas, numpy.array(ibm_dpl_mean)-0.5*numpy.array(ibm_dpl_stdev), numpy.array(ibm_dpl_mean)+0.5*numpy.array(ibm_dpl_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)

    ax1.set_xlabel("Sigma")
    ax1.set_ylabel("Sampling Time (ms)")
    plt.legend(loc = 'best')
    now = datetime.now()
    filename = 'GaussianBenchmarks' + now.strftime("%H%M%S") + '.pdf'
    plt.savefig(filename)

if __name__ == "__main__":
    gaussian_benchmarks()
