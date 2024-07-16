#!/usr/bin/env python3

# Benchmarking the implementations of DiscreteLaplaceSample and DiscreteLaplaceSample'
# Based on the benchmarks in Dafny-VMC

import SampCert
import matplotlib.pyplot as plt
import timeit
import numpy
from datetime import datetime

from diffprivlib.mechanisms.base import bernoulli_neg_exp
from diffprivlib.mechanisms import GaussianDiscrete


# source: https://github.com/IBM/discrete-gaussian-differential-privacy
from fractions import Fraction
from discretegauss import sample_dlaplace


sampler = SampCert.SLang()

# Compute the discrete laplacian value from an IBM DiscreteGaussian object
# Only works when eps is an integer, ie. compute the same value as DiscreteLaplaceSample(1, eps)
def ibm_lap (g, eps):
    # if g._scale == 0:
    #     return value
    tau = eps
    # tau = 1 / (1 + numpy.floor(g._scale))
    # sigma2 = g._scale ** 2
    while True:
        geom_x = 0
        while bernoulli_neg_exp(tau, g._rng):
            geom_x += 1
        bern_b = g._rng.random() < 0.5
        if bern_b and not geom_x:
            continue
        lap_y = int((1 - 2 * bern_b) * geom_x)
        return lap_y
        # bern_c = bernoulli_neg_exp((abs(lap_y) - tau * sigma2) ** 2 / 2 / sigma2, g._rng)
        # if bern_c:
        #     return value + lap_y


def create_histogram(samples):
    """Returns a pair of arrays (values,counts), where size(values)=size(counts),
    corresponding to the (sorted) unique values seen in the sample along with the
    number of times they appear."""
    samples.sort()
    values=[]
    counts=[]
    counter=None
    prev=None
    for sample in samples:
        if prev is None: #initializing
            prev=sample
            counter=1
        elif sample==prev: #still same element
            counter=counter+1
        else:
            #add prev to histogram
            values.append(prev)
            counts.append(counter)
            #start counting
            prev=sample
            counter=1
    #add final value
    values.append(prev)
    counts.append(counter)
    return (values,counts)







# Check that the various samplers are computing the same thing
def check_pmfs():
    eps = 2
    N = 500000
    g = GaussianDiscrete(epsilon=eps, delta=0.00001)
    ss = []
    ss2 = []
    ss3 = []
    for i in range(N):
        ss.append(ibm_lap(g, eps))
        ss2.append(sampler.DiscreteLaplaceSample(1, eps))
        ss3.append(sample_dlaplace(1 / eps))
    w = create_histogram(ss)
    w2 = create_histogram(ss2)
    w3 = create_histogram(ss3)
    fig,ax3 = plt.subplots()
    ax3.plot(w[0], [float(i) / float(N) for i in w[1]], label='Calculated')
    ax3.plot(w2[0], [float(i) / float(N) for i in w2[1]], label='Lean')
    ax3.plot(w3[0], [float(i) / float(N) for i in w3[1]], label='sample_dlaplace')
    ax3.plot(w[0], [numpy.exp(float(abs(k)) * (-1.0) * eps ) * (numpy.exp(eps) - 1.0) / (numpy.exp(eps) + 1.0) for k in w[0]], label='Predicted')
    plt.legend(loc='best')
    plt.savefig("test.pdf")





# Make a plot comparing their runtime at integer values
def integer_plots():
    eps = []

    lap_mean = []
    lap_stdev = []
    lapO_mean = []
    lapO_stdev = []
    dpl_mean = []
    dpl_stdev = []

    max_den = 100

    # Number of attempts for each value of epsilon:
    warmup_attempts = 100
    measured_attempts = 500
    num_attempts = warmup_attempts + measured_attempts

    for den in range(1, max_den):
        print("Sampling {}/{}".format(den, max_den))

        eps.append(1/den)

        t_lap = []
        t_lapO = []
        t_lapDPL = []

        # Time DiscreteLaplaceSample
        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sampler.DiscreteLaplaceSample(1, den)
            elapsed = timeit.default_timer() - start_time
            t_lap.append(elapsed)

        # Time DiscreteLaplaceSampleOpt
        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sampler.DiscreteLaplaceSampleOpt(1, den)
            elapsed = timeit.default_timer() - start_time
            t_lapO.append(elapsed)

        # Time other IBM implementation
        for i in range(num_attempts):
            ibm_g = GaussianDiscrete(epsilon=den, delta=0.00001)
            start_time = timeit.default_timer()
            ibm_lap(ibm_g, den)
            elapsed = timeit.default_timer() - start_time
            t_lapDPL.append(elapsed)

        # Compute mean and stdev
        lap_measured = numpy.array(t_lap[-measured_attempts:])
        lapO_measured = numpy.array(t_lapO[-measured_attempts:])
        lapDPL_measured = numpy.array(t_lapDPL[-measured_attempts:])

        lap_mean.append(lap_measured.mean() * 1000.0)
        lap_stdev.append(lap_measured.std() * 1000.0)
        lapO_mean.append(lapO_measured.mean() * 1000.0)
        lapO_stdev.append(lapO_measured.std() * 1000.0)
        dpl_mean.append(lapDPL_measured.mean() * 1000.0)
        dpl_stdev.append(lapDPL_measured.std() * 1000.0)

    # Graph of LaplaceOpt vs the two implementations, and IBM
    fig,ax2 = plt.subplots()
    ax2.fill_between(eps, numpy.array(lapO_mean)-0.5*numpy.array(lapO_stdev), numpy.array(lapO_mean)+0.5*numpy.array(lapO_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)
    ax2.plot(eps, lap_mean, color='red', linewidth=1.0, linestyle="solid", label='DiscreteLaplaceSample')
    ax2.plot(eps, lapO_mean, color='black', linewidth=2.0, linestyle="solid", label='DiscreteLaplaceSampleOpt')
    ax2.plot(eps, dpl_mean, color='orange', linewidth=1.0, linestyle="solid", label='IBM diffprivlib (inlined)')
    ax2.set_xlabel("1/Epsilon")
    ax2.set_ylabel("Sampling Time (ms)")
    plt.legend(loc = 'best')
    now = datetime.now()
    filename = 'IntLaplaceComparison' + now.strftime("%H%M%S") + '.pdf'
    plt.savefig(filename)



if __name__ == "__main__":
    print("=========================================================================\n\
Benchmark: Obtaining the empirical threshold where DiscreteLaplaceSample \n\
becomes more efficient than DiscreteLaplaceSample'. \n\
=========================================================================")
    integer_plots()
    exit(1)

    # check_pmfs()
    # exit(1)


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

    # Timing results for IBM diffprivlib
    ibm_dpl_mean = []
    ibm_dpl_stdev = []

    # Range of epsilon parameters to try
    den = 8
    num_eps = 250

    # Number of attempts for each value of epsilon:
    warmup_attempts = 100
    measured_attempts = 2000
    num_attempts = warmup_attempts + measured_attempts


    for num in range(1, num_eps):
        print ("Sample {}/{}".format(num, num_eps))

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
        # ibm_dpl_mean.append(lapDPL_measured.mean() * 1000.0)
        # ibm_dpl_stdev.append(lapDPL_measured.std() * 1000.0)


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
    # ax2.plot(eps, ibm_dpl_mean, color='orange', linewidth=1.0, linestyle="solid", label='IBM diffprivlib')
    ax2.set_xlabel("Epsilon")
    ax2.set_ylabel("Sampling Time (ms)")
    plt.legend(loc = 'best')
    now = datetime.now()
    filename = 'LaplaceOptBenchmark' + now.strftime("%H%M%S") + '.pdf'
    plt.savefig(filename)
