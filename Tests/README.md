# Tests and benchmarks

Compile the tests
```
lake build FastExtract
dafny build --target:py Tests/SampCert.dfy Tests/Random.py Tests/testing-kolmogorov-discretegaussian.py Tests/testing-kolmogorov-discretelaplace.py Tests/IBM/discretegauss.py Tests/benchmarks.py -o Tests/SampCert.dfy
```

Then, 
- Calculate a KS stastic on the Discrete Gaussian sampler: 
	```python3 Tests/SampCert-py/testing-kolmogorov-discretegaussian.py```
- Calculate a KS stastic on the Discrete Laplace sampler: 
	```python3 Tests/SampCert-py/testing-kolmogorov-discretelaplace.py```
- Generate benchmarking plots for the Discrete Gaussian sampler
	```python3 Tests/SampCert-py/benchmarks.py```
