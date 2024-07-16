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

def laplace_benchmarks():
    print("=========================================================================\n\
Benchmark: Obtaining the empirical threshold where DiscreteLaplaceSample \n\
becomes more efficient than DiscreteLaplaceSample'. \n\
=========================================================================")
    # Values of epsilon attempted
    eps = []

    # Timing results for DiscreteLaplaceSample
    lap_mean = []
    lap_stdev = []

    # Timing results for DiscreteLaplaceSample'
    lap1_mean = []
    lap1_stdev = []

    # Timing results for DiscreteLaplaceOpt
    lapO_mean = []
    lapO_stdev = []

    # Timing results for IBM implementation sample_dlaplace
    ibm_mean = []
    ibm_stdev = []

    # Range of epsilon parameters to try
    den = 8
    num_eps = 250

    # Number of attempts for each value of epsilon:
    warmup_attempts = 100
    measured_attempts = 2000
    num_attempts = warmup_attempts + measured_attempts

    for num in tqdm.tqdm(range(1, num_eps)):

        eps.append(num/den)
        t_lap = []
        t_lap1 = []
        t_lapO = []
        t_lapIBM = []
        t_lapDPL = []

        # Time DiscreteLaplaceSample
        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sampler.DiscreteLaplaceSample(num, den)
            elapsed = timeit.default_timer() - start_time
            t_lap.append(elapsed)

        # Time DiscreteLaplaceSample'
        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sampler.DiscreteLaplaceSample_k(num, den)
            elapsed = timeit.default_timer() - start_time
            t_lap1.append(elapsed)

        # Time DiscreteLaplaceSampleOpt
        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sampler.DiscreteLaplaceSampleOpt(num, den)
            elapsed = timeit.default_timer() - start_time
            t_lapO.append(elapsed)

        # Time IBM implementation
        for i in range(num_attempts):
            ep = Fraction(num/den)
            start_time = timeit.default_timer()
            sample_dlaplace(ep)
            elapsed = timeit.default_timer() - start_time
            t_lapIBM.append(elapsed)


        # Compute mean and stdev
        lap_measured = numpy.array(t_lap[-measured_attempts:])
        lap1_measured = numpy.array(t_lap1[-measured_attempts:])
        lapO_measured = numpy.array(t_lapO[-measured_attempts:])
        lapIBM_measured = numpy.array(t_lapIBM[-measured_attempts:])
        lapDPL_measured = numpy.array(t_lapDPL[-measured_attempts:])

        # Convert s to ms
        lap_mean.append(lap_measured.mean() * 1000.0)
        lap_stdev.append(lap_measured.std() * 1000.0)
        lap1_mean.append(lap1_measured.mean() * 1000.0)
        lap1_stdev.append(lap1_measured.std() * 1000.0)
        lapO_mean.append(lapO_measured.mean() * 1000.0)
        lapO_stdev.append(lapO_measured.std() * 1000.0)
        ibm_mean.append(lapIBM_measured.mean() * 1000.0)
        ibm_stdev.append(lapIBM_measured.std() * 1000.0)

    # Graph of the two laplace implementations, with threshold
    fig,ax1 = plt.subplots()

    ax1.plot(eps, lap_mean, color='red', linewidth=1.0, label='DiscreteLaplaceSample')
    ax1.fill_between(eps, numpy.array(lap_mean)-0.5*numpy.array(lap_stdev), numpy.array(lap_mean)+0.5*numpy.array(lap_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)

    ax1.plot(eps, lap1_mean, color='blue', linewidth=1.0, label='DiscreteLaplaceSample\'')
    ax1.fill_between(eps, numpy.array(lap1_mean)-0.5*numpy.array(lap1_stdev), numpy.array(lap1_mean)+0.5*numpy.array(lap1_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)

    # Find the last index of epsilon where DiscreteLaplaceSample beats DiscreteLaplaceSample'
    eps_thresh_index = len(eps) - numpy.argmax(numpy.flip(numpy.array(lap_mean) < numpy.array(lap1_mean))) - 1
    ax1.axvline(x = eps[eps_thresh_index], color = 'orange', linewidth=1, linestyle='dashed', label = "Threshold: {}".format(eps[eps_thresh_index]))

    ax1.set_xlabel("Epsilon")
    ax1.set_ylabel("Sampling Time (ms)")
    plt.legend(loc = 'best')
    now = datetime.now()
    filename = 'LaplaceBenchmarks' + now.strftime("%H%M%S") + '.pdf'
    plt.savefig(filename)


    # Graph of LaplaceOpt vs the two implementations, and IBM
    fig,ax2 = plt.subplots()
    ax2.fill_between(eps, numpy.array(lapO_mean)-0.5*numpy.array(lapO_stdev), numpy.array(lapO_mean)+0.5*numpy.array(lapO_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)
    ax2.plot(eps, lap_mean, color='red', linewidth=1.0, linestyle="solid", label='DiscreteLaplaceSample')
    ax2.plot(eps, lap1_mean, color='blue', linewidth=1.0, linestyle="solid", label='DiscreteLaplaceSample\'')
    ax2.plot(eps, lapO_mean, color='black', linewidth=2.0, linestyle="solid", label='DiscreteLaplaceSampleOpt')
    ax2.plot(eps, ibm_mean, color='purple', linewidth=1.0, linestyle="solid", label='IBM sample_dlaplace')
    ax2.set_xlabel("Epsilon")
    ax2.set_ylabel("Sampling Time (ms)")
    plt.legend(loc = 'best')
    now = datetime.now()
    filename = 'LaplaceOptBenchmark' + now.strftime("%H%M%S") + '.pdf'
    plt.savefig(filename)


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
    # laplace_benchmarks()
    gaussian_benchmarks()
