#!/usr/bin/env python

#Testing code for discrete Gaussian sampler
# - Clement Canonne 2020
# With some modifications for SampCert

# Import the discrete Gaussian sampling implementation
import SampCert
import argparse

sampler = SampCert.SLang() 

num = 4
den = 1
sig = float(num) / float(den)
sig2 = sig*sig
N = 10000

def sample_dgauss(): 
    return sampler.DiscreteGaussianSample(num,den,0)

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


def cdf_eval(k,normcst,sigma2):
    """Takes as input an integer k, along with the normalizing constant
                  sum_n e^(-n^2/2sigma^2)
    and the value of the (squared) scale parameter sigma^2.
    Returns the value of the cdf evaluated at k."""
    
    bounds = max(50*sigma2,10000)  # Compute the CDF starting at -bounds instead of -infty (negligible error)
    return np.sqrt(2*np.pi*sigma2)*sum( [stats.norm.pdf(n, loc=0, scale=np.sqrt(sigma2)) for n in range(-bounds,k+1)] )/normcst


# Main test function
def test_kolmogorov_dist(N, sigma2, with_plots=False):
    """Takes as input a sample size N, the desired (squared) scale parameter sigma^2
    for the discrete Gaussian, and whether the function should plot the empirical
    distribution and the cdf or not along the way.
    
    Returns the Kolmogorov distance (L_inf distance between CDFs) between the empirical
    CDF and the true CDF (value between 0 and 1).
    
    Note that this is a random variable, as the empirical CDF depends on the sample drawn."""
    
    x = [sample_dgauss() for i in range(N)] # Draw the N samples from our discrete Gaussian sampler
    (v,c) = create_histogram(x)
    
    # Compute the normalizing constant fromt -bounds to bounds instead of -infty to infty:
    # negligible error, as bounds is at least 50 standard deviations from 0, and the tails
    # decay exponentially.
    bounds = max(50*sigma2,10000) 
    normcst = np.sqrt(2*np.pi*sigma2)*sum( [stats.norm.pdf(n, loc=0, scale=np.sqrt(sigma2)) for n in range(-bounds,bounds)] )
    
    # Compute the empirical CDF (from the histogram) and the true CDF evaluated at those points
    ecdf = np.cumsum(c)/N
    truecdf = [cdf_eval(k,normcst,sigma2) for k in v]

    # Plot the empirical distribution and the CDFs (empirical and true) if we must
    if with_plots:
        # Empirical histogram
        plt.figure(figsize=(12,9),dpi=200)
        plt.bar(v, c)
        plt.title("Empirical pmf ($\sigma^2=%.2f, N=%d$)" % (sigma2,N))
        plt.show()
        
        # CDF (true and empirical)
        plt.figure(figsize=(12,9),dpi=200)
        plt.plot(v,ecdf, label="Empirical")
        plt.plot(v,truecdf, label="True")
        plt.legend(loc="upper left")
        plt.title("True and empirical cdf ($\sigma^2=%.2f, N=%d$)" % (sigma2,N))
        plt.show()
    
    # Kolmogorov distance: sup_x |CDF1(x) - CDF2(x)|
    kolmorogov_dist = np.max(abs(truecdf-ecdf))
    print("Kolmogorov distance: %.5f" % kolmorogov_dist)
    return kolmorogov_dist

if __name__ == "__main__":

    print("=========================================================================\n\
    Testing: assessing that the distribution implemented is indeed the\n\
    discrete Gaussian by computing the Kolmogorov-Smirnov statistic and\n\
    showing it converges to 0 as the sample size increases.\n\
    \n\
    The K-S statistic is the Kolmogorov distance (i.e., L_inf distance between \n\
    CDF) between the empirical and true distributions. It is a value in [0,1], \n\
    where 0 indicates equality and 1 maximal distance. \n\
    =========================================================================")

    print("\n")

    parser = argparse.ArgumentParser()
    parser.add_argument('-i', action="store_true", default=False)
    args = parser.parse_args()

    if args.i:
        print("\n")

        # How to use the "test_kolmogorov_dist" function: on N=2000 samples, with sigma^2 = 10
        print("* Calling the 'test_kolmogorov_dist' function with N=2000 and location parameter sigma^2=10 (with plots):")
        test_kolmogorov_dist(N,sig2,True);

        print("\n")

        # Now compute the distances for various N's, evenly spaced (on a log scale) from 10
        # to 10^7 for sigma^2 = 20 (arbitrary choice)
        print("* Calling the 'test_kolmogorov_dist' function with N ranging from 10 to 10^7, 50 values\n\
        evenly spaced on the log scale, and location parameter sigma^2=20:")
        distances = [test_kolmogorov_dist(int(N),sig2) for N in np.logspace(1.0, 7.0, num=50)];

        # Plot the result (on a loglog scale)
        plt.figure(figsize=(12,9),dpi=200)
        plt.loglog(np.logspace(1.0, 7.0, num=50),distances, '-o')
        plt.title("Kolmogorov distance between true and empirical ($\sigma^2=20$)")
        plt.xlabel("Sample size N")
        plt.ylabel("Kolmogorov distance")
        plt.show()
    else:  
        print("* Calling the 'test_kolmogorov_dist' function with N=1000 and location parameter sigma^2=10 (without plots):")
        # How to use the "test_kolmogorov_dist" function: on N=10000 samples, with sigma^2 = 10 (no plots)
        diff = test_kolmogorov_dist(N,sig2)
        if diff < 0.02:
            print("Test passed!")
            exit(0)
        else: 
            print("Test failed!")
            exit(1)

