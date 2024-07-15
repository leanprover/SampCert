#!/usr/bin/env python3

# Benchmarking the implementations of DiscreteLaplaceSample and DiscreteLaplaceSample'
# Based on the benchmarks in Dafny-VMC

import SampCert
import matplotlib.pyplot as plt
import timeit
import numpy
from datetime import datetime

sampler = SampCert.SLang()

if __name__ == "__main__":
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

    # Range of epsilon parameters to try
    den = 8
    num_eps = 500

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

        # Time DiscreteLaplaceSample
        for i in range(num_attempts):
            start_time = timeit.default_timer()
            sampler.DiscreteLaplaceSample(num, den)
            elapsed = timeit.default_timer() - start_time
            t_lap.append(elapsed)

        # Time DiscreteLaplaceSample'
        for i in range(num_attempts):
            start_time1 = timeit.default_timer()
            sampler.DiscreteLaplaceSample_k(num, den)
            elapsed1 = timeit.default_timer() - start_time1
            t_lap1.append(elapsed1)

        # Time DiscreteLaplaceSampleOpt
        for i in range(num_attempts):
            start_timeO = timeit.default_timer()
            sampler.DiscreteLaplaceSampleOpt(num, den)
            elapsedO = timeit.default_timer() - start_timeO
            t_lapO.append(elapsedO)

        # Compute mean and stdev
        lap_measured = numpy.array(t_lap[-measured_attempts:])
        lap1_measured = numpy.array(t_lap1[-measured_attempts:])
        lapO_measured = numpy.array(t_lapO[-measured_attempts:])

        # Convert s to ms
        lap_mean.append(lap_measured.mean() * 1000.0)
        lap_stdev.append(lap_measured.std() * 1000.0)
        lap1_mean.append(lap1_measured.mean() * 1000.0)
        lap1_stdev.append(lap1_measured.std() * 1000.0)
        lapO_mean.append(lapO_measured.mean() * 1000.0)
        lapO_stdev.append(lapO_measured.std() * 1000.0)


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


    # Graph of LaplaceOpt vs the two implementations
    fig,ax2 = plt.subplots()
    ax2.fill_between(eps, numpy.array(lapO_mean)-0.5*numpy.array(lapO_stdev), numpy.array(lapO_mean)+0.5*numpy.array(lapO_stdev),
                     alpha=0.2, facecolor='k', linewidth=2, linestyle='dashdot', antialiased=True)
    ax2.plot(eps, lap_mean, color='red', linewidth=1.0, linestyle="solid", label='DiscreteLaplaceSample')
    ax2.plot(eps, lap1_mean, color='blue', linewidth=1.0, linestyle="solid", label='DiscreteLaplaceSample\'')
    ax2.plot(eps, lapO_mean, color='black', linewidth=2.0, linestyle="solid", label='DiscreteLaplaceSampleOpt')
    ax2.set_xlabel("Epsilon")
    ax2.set_ylabel("Sampling Time (ms)")
    plt.legend(loc = 'best')
    now = datetime.now()
    filename = 'LaplaceOptBenchmark' + now.strftime("%H%M%S") + '.pdf'
    plt.savefig(filename)
