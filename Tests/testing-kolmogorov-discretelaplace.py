#!/usr/bin/env python

# Testing code for discrete Laplace samplers
# Modified from KS testing code by Clement Canonne 2020

# Import the discrete Gaussian sampling implementation
import SampCert
import argparse

sampler = SampCert.SLang() 

num = 4
den = 1
eps = float(num) / float(den)
N = 10000


def sample_lap():
    return sampler.DiscreteLaplaceSample(num, den)

def sample_lap1():
    return sampler.DiscreteLaplaceSampleMixed(num, den, 7)

def sample_lapO():
    return sampler.DiscreteLaplaceSampleOptimized(num, den)

#################################
############ Testing ############
#################################

# Import the necessary packages
import matplotlib.pyplot as plt
import numpy as np
from scipy import stats

# Helper functions
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

def pmf_eval(k):
    """Takes as input an integer kand returns the value of the
    discrete Laplace pmf evaluated at k.
    """
    return np.exp(float(abs(k)) * (-1.0) / eps ) * (np.exp(1/eps) - 1.0) / (np.exp(1/eps) + 1.0)

def cdf_eval(k):
    """Takes as input an integer k, and returns the value of the
    discrete Laplace cdf evaluated at k.
    """
    # acc starts as the CDF at x = 0
    acc = 1.0/2.0 + pmf_eval(0) / 2.0
    if k < 0:
        for i in range(0, -k):
            acc -= pmf_eval(i)
    elif k > 0:
        for i in range(1, k+1):
            acc += pmf_eval(i)
    return acc


# Main test function
def test_kolmogorov_dist(N, with_plots=False, sampler=0):
    """Takes as input a sample size N, the desired parameter epsilon for the
    discrete Laplace distribution, and whether the function should plot the empirical
    distribution and the cdf or not along the way.
    
    Returns the Kolmogorov distance (L_inf distance between CDFs) between the empirical
    CDF and the true CDF (value between 0 and 1).
    
    Note that this is a random variable, as the empirical CDF depends on the sample drawn."""
    if sampler == 0:
        x = [sample_lap() for i in range(N)]
    elif sampler == 1:
        x = [sample_lap1() for i in range(N)]
    elif sampler == 2:
        x = [sample_lapO() for i in range(N)]
    else:
        print("Invalid sampler")
        exit(1)

    (v,c) = create_histogram(x)
    true_pmf = [pmf_eval(k) for k in v]

    # Compute the empirical CDF (from the histogram) and the true CDF evaluated at those points
    ecdf = np.cumsum(c)/N
    truecdf = [cdf_eval(k) for k in v]

    # Plot the empirical distribution and the CDFs (empirical and true) if we must
    if with_plots:
        # Histogram
        plt.figure(figsize=(12,9),dpi=200)
        plt.plot(v, [c1 / N for c1 in c], color='blue', label='empirical')
        plt.plot(v, true_pmf, color='red', label='true')
        plt.title("Empirical pmf ($\epsilon=%.2f, N=%d$)" % (eps,N))
        plt.legend(loc = 'best')
        plt.savefig("histogram.pdf")

        # CDF (true and empirical)
        plt.figure(figsize=(12,9),dpi=200)
        plt.plot(v,ecdf, label="Empirical")
        plt.plot(v,truecdf, label="True")
        plt.legend(loc="upper left")
        plt.title("True and empirical cdf ($\epsilon=%.2f, N=%d$)" % (eps,N))
        plt.savefig("cdf.pdf")

    # Kolmogorov distance: sup_x |CDF1(x) - CDF2(x)|
    kolmorogov_dist = np.max(abs(truecdf-ecdf))
    print("Kolmogorov distance: %.5f" % kolmorogov_dist)
    return kolmorogov_dist

if __name__ == "__main__":

    print("=========================================================================\n\
Testing: assessing that the distribution implemented is indeed the\n\
discrete Laplace by computing the Kolmogorov-Smirnov statistic and\n\
showing it converges to 0 as the sample size increases.\n\
\n\
The K-S statistic is the Kolmogorov distance (i.e., L_inf distance between \n\
CDF) between the empirical and true distributions. It is a value in [0,1], \n\
where 0 indicates equality and 1 maximal distance. \n\
=========================================================================")
    parser = argparse.ArgumentParser()
    parser.add_argument('-i', action="store_true", default=False)
    args = parser.parse_args()

    if args.i:
        print("\n")

        # How to use the "test_kolmogorov_dist" function: on N=2000 samples, with eps=4
        print("* Calling the 'test_kolmogorov_dist' function with N=2000 and location parameter eps=4 (with plots):")
        test_kolmogorov_dist(N,True);

        print("\n")

        # Now compute the distances for various N's, evenly spaced (on a log scale) from 10
        # to 10^7 for eps = 20 (arbitrary choice)
        print("* Calling the 'test_kolmogorov_dist' function with N ranging from 10 to 10^7, 50 values\n\
        evenly spaced on the log scale, and parameter eps=4:")
        distances = [test_kolmogorov_dist(int(N)) for N in np.logspace(1.0, 7.0, num=50)];

        # Plot the result (on a loglog scale)
        plt.figure(figsize=(12,9),dpi=200)
        plt.loglog(np.logspace(1.0, 7.0, num=50),distances, '-o')
        plt.title("Kolmogorov distance between true and empirical ($\epsilon = 4$)")
        plt.xlabel("Sample size N")
        plt.ylabel("Kolmogorov distance")
        plt.show()
    else:  
        print("* Calling the 'test_kolmogorov_dist' function with N=1000 and location parameter eps=4 (without plots):")
        diff = test_kolmogorov_dist(N, sampler=0)
        diff1 = test_kolmogorov_dist(N, sampler=1)
        diffO = test_kolmogorov_dist(N, sampler=2)
        if diff < 0.02:
            print("DiscreteLaplaceSample Test passed!")
        else:
            print("Test failed!")
            exit(1)
        if diff1 < 0.02:
            print("DiscreteLaplaceSampleOptimized Test passed!")
        else:
            print("Test failed!")
            exit(1)
        if diffO < 0.02:
            print("DiscreteLaplaceSampleMixed Test passed!")
        else:
            print("Test failed!")
            exit(1)
        exit(0)
