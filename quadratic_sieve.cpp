#include <iostream>
#include <gmpxx.h>
#include <cstdlib>
#include <cmath>
#include <vector>
#include <stack>

// How large chunks should we sieve at a time?
const uint32_t SIEVE_CHUNK = 65536;

// How small large integers should we run trial division on?
const uint32_t TRIAL_BOUND = 1000000000;

uint64_t pow_mod(uint64_t a, uint64_t b, uint64_t m);
int32_t legendre_symbol(uint32_t a, uint32_t p);
void tonelli_shanks(uint32_t n, uint32_t p, uint32_t *result);
mpz_class quadratic_sieve(mpz_class &N);

// Modular exponentiation using the right-to-left binary method.
uint64_t pow_mod(uint64_t a, uint64_t b, uint64_t m) {
	uint64_t r = 1;
	while(b > 0) {
		if(b & 1)
			r = r * a % m;
		b >>= 1;
		a = a * a % m;
	}

	return r;
}

int32_t legendre_symbol(uint32_t a, uint32_t p) {
	unsigned long t = pow_mod(a, (p - 1) / 2, p);
	return t > 1 ? -1 : t;
}

// Solve the congruence x^2 = n (mod p).
void tonelli_shanks(uint32_t n, uint32_t p, uint32_t *result) {
	if(p == 2) {
		result[0] = n;
		result[1] = n;
		return;
	}

	uint64_t S = 0;
	uint64_t Q = p - 1;

	while(Q % 2 == 0) {
		Q /= 2;
		++S;
	}

	uint64_t z = 2;

	while(legendre_symbol(z, p) != -1)
		++z;

	uint64_t c = pow_mod(z, Q, p);
	uint64_t R = pow_mod(n, (Q + 1) / 2, p);
	uint64_t t = pow_mod(n, Q, p);
	uint64_t M = S;

	while(t % p != 1) {
		int32_t i = 1;
		while(pow_mod(t, pow(2, i), p) != 1)
			++i;
	
		uint64_t b = pow_mod(c,  pow(2, M - i - 1), p);
		R = R * b % p;
		t = t * b * b % p;
		c = b * b % p;
		M = i;
	}

	result[0] = R;
	result[1] = p - R;
}

// Get the i'th bit in row.
inline int32_t get_bit(uint32_t i, uint64_t *row) {
	return (row[i / sizeof(uint64_t)] & (1 << (i % sizeof(uint64_t)))) != 0;
}

// Set the i'th bit in row to 1.
inline void set_bit(uint32_t i, uint64_t *row) {
	row[i / sizeof(uint64_t)] |= (1 << (i % sizeof(uint64_t)));
}

// Set the i'th bit in row to 0.
inline void unset_bit(uint32_t i, uint64_t *row) {
	row[i / sizeof(uint64_t)] &= ~(1 << (i % sizeof(uint64_t)));
}

// Toggle the i'th bit in row.
inline void toggle_bit(uint32_t i, uint64_t *row) {
	row[i / sizeof(uint64_t)] ^= (1 << (i % sizeof(uint64_t)));
}

// A quadratic sieve implementation for integers up to 100 bits. N must be composite.
mpz_class quadratic_sieve(mpz_class &N) {
	std::vector<uint32_t> factor_base;

	mpz_class sqrt_N = sqrt(N);
	//const unsigned long sqrt_N_long = sqrt_N.get_ui();

	// Set the smoothness bound.
	uint32_t B;
	{
		// Approximation of the natural logarithm of N.
		float log_N = mpz_sizeinbase(N.get_mpz_t(), 2) * log(2);

		// The optimal smoothness bound is exp((0.5 + o(1)) * sqrt(log(n)*log(log(n)))).
		B = (uint32_t)ceil(exp(0.56 * sqrt(log_N * log(log_N)))) + 300;
	}

	// Generate the factor base using a sieve.
	{
		char *sieve = new char[B + 1];
		memset(sieve, 1, B + 1);
		for(unsigned long p = 2; p <= B; ++p) {
			if(!sieve[p])
				continue;

			if(mpz_legendre(N.get_mpz_t(), mpz_class(p).get_mpz_t()) == 1)
				factor_base.push_back(p);

			for(unsigned long i = p; i <= B; i += p)
				sieve[i] = 0;
		}
		delete[] sieve;
	}

	std::vector<uint32_t> X;
	float *Y = new float[SIEVE_CHUNK];

	std::vector<std::vector<uint32_t> > smooth;

	int fails = 0;

	// The sieve boundary.
	uint32_t min_x = 0;
	uint32_t max_x = SIEVE_CHUNK;

	// Calculate sieve index (where to start the sieve) for each factor base number.
	uint32_t **fb_indexes = new uint32_t*[2];
	fb_indexes[0] = new uint32_t[factor_base.size()];
	fb_indexes[1] = new uint32_t[factor_base.size()];
	for(uint32_t p = 0; p < factor_base.size(); ++p) {
		// At what indexes do we start this sieve? Solve the congruence x^2 = n (mod p) to find out.
		// Results in two solutions, so we do two sieve iterations for each prime in the factor base.
		uint32_t idxs[2];
		mpz_class temp = N % mpz_class(factor_base[p]);
		tonelli_shanks(temp.get_ui(), factor_base[p], idxs);

		temp = idxs[0] - sqrt_N;
		temp = ((temp % factor_base[p]) + factor_base[p]) % factor_base[p];
		fb_indexes[0][p] = temp.get_ui();

		temp = idxs[1] - sqrt_N;
		temp = ((temp % factor_base[p]) + factor_base[p]) % factor_base[p];
		fb_indexes[1][p] = temp.get_ui();
	}

	float last_estimate = 0;
	uint32_t next_estimate = 1;

	// Sieve new chunks until we have enough smooth numbers.
	while(smooth.size() < (factor_base.size() + 20)) {
		// Generate our Y vector for the sieve, containing log approximations that fit in machine words.
		for(uint32_t t = 1; t < SIEVE_CHUNK; ++t) {
			// Calculating a log estimate is expensive, so don't do it for every Y[t].
			if(next_estimate <= (t + min_x)) {
				mpz_class y = (sqrt_N + t + min_x) * (sqrt_N + t + min_x) - N;

				// To estimate the 2 logarithm, just count the number of bits that v takes up.
				last_estimate = mpz_sizeinbase(y.get_mpz_t(), 2);

				// The higher t gets, the less the logarithm of Y[t] changes.
				next_estimate = next_estimate * 1.8 + 1;
			}

			Y[t] = last_estimate;
		}

		// Perform the actual sieve.
		for(uint32_t p = 0; p < factor_base.size(); ++p) {
			float lg = log(factor_base[p]) / log(2);

			for(uint32_t t = 0; t < 2; ++t) {
				while(fb_indexes[t][p] < max_x) {
					Y[fb_indexes[t][p] - min_x] -= lg;
					fb_indexes[t][p] += factor_base[p];
				}

				// p = 2 only has one modular root.
				if(factor_base[p] == 2)
					break;
			}
		}

		// Factor all values whose logarithms were reduced to approximately zero using trial division.
		{
			float threshold = log(factor_base.back()) / log(2);
			for(uint32_t i = 0; i < SIEVE_CHUNK; ++i) {
				if(fabs(Y[i]) < threshold) {
					mpz_class y = (sqrt_N + i + min_x) * (sqrt_N + i + min_x) - N;
					smooth.push_back(std::vector<uint32_t>());

					for(uint32_t p = 0; p < factor_base.size(); ++p) {
						while(mpz_divisible_ui_p(y.get_mpz_t(), factor_base[p])) {
							mpz_divexact_ui(y.get_mpz_t(), y.get_mpz_t(), factor_base[p]);
							smooth.back().push_back(p);
						}
					}

					if(y == 1) {
						// This V was indeed B-smooth.
						X.push_back(i + min_x);
						
						// Break out of trial division loop if we've found enou	gh smooth numbers.
						if(smooth.size() >= (factor_base.size() + 20))
							break;
					} else {
						// This V was apparently not B-smooth, remove it.
						smooth.pop_back();
						++fails;
					}
				}
			}
		}

		min_x += SIEVE_CHUNK;
		max_x += SIEVE_CHUNK;
	}

	uint64_t **matrix = new uint64_t*[factor_base.size()];

	// The amount of words needed to accomodate a row in the augmented matrix.
	int row_words = (smooth.size() + sizeof(uint64_t)) / sizeof(uint64_t);

	for(uint32_t i = 0; i < factor_base.size(); ++i) {
		matrix[i] = new uint64_t[row_words];
		memset(matrix[i], 0, row_words * sizeof(uint64_t));
	}

	for(uint32_t s = 0; s < smooth.size(); ++s) {
		// For each factor in the smooth number, add the factor to the corresponding element in the matrix.
		for(uint32_t p = 0; p < smooth[s].size(); ++p)
			toggle_bit(s, matrix[smooth[s][p]]);
	}

	// Gauss elimination. The dimension of the augmented matrix is factor_base.size() x (smooth.size() + 1).
	{
		uint32_t i = 0, j = 0;
		while(i < factor_base.size() && j < (smooth.size() + 1)) {
			uint32_t maxi = i;

			// Find pivot element.
			for(uint32_t k = i + 1; k < factor_base.size(); ++k) {
				if(get_bit(j, matrix[k]) == 1) {
					maxi = k;
					break;
				}
			}
			if(get_bit(j, matrix[maxi]) == 1) {
				std::swap(matrix[i], matrix[maxi]);
				
				for(uint32_t u = i + 1; u < factor_base.size(); ++u) {
					if(get_bit(j, matrix[u]) == 1) {
						for(int32_t w = 0; w < row_words; ++w)
							matrix[u][w] ^= matrix[i][w];
					}
				}
				++i;
			}
			++j;
		}
	}

	mpz_class a;
	mpz_class b;

	// A copy of matrix that we'll perform back-substitution on.
	uint64_t **back_matrix = new uint64_t*[factor_base.size()];
	for(uint32_t i = 0; i < factor_base.size(); ++i)
		back_matrix[i] = new uint64_t[row_words];

	uint32_t *x = new uint32_t[smooth.size()];

	uint32_t *combination = new uint32_t[factor_base.size()];

	// Loop until we've found a non-trivial factor.
	do {
		// Copy the gauss eliminated matrix.
		for(uint32_t i = 0; i < factor_base.size(); ++i)
			memcpy(back_matrix[i], matrix[i], row_words * sizeof(uint64_t));

		// Clear the x vector.
		memset(x, 0, smooth.size() * sizeof(uint32_t));

		// Perform back-substitution on our matrix that's now in row echelon form to get x.
		{
			int32_t i = factor_base.size() - 1;

			while(i >= 0) {
				// Count non-zero elements in current row.
				int32_t count = 0;
				int32_t current = -1;
				for(uint32_t c = 0; c < smooth.size(); ++c) {
					count += get_bit(c, back_matrix[i]);
					current = get_bit(c, back_matrix[i]) ? c : current;
				}

				// Empty row, advance to next.
				if(count == 0) {
					--i;
					continue;
				}

				// The system is underdetermined and we can choose x[current] freely.
				// To avoid the trivial solution we avoid always setting it to 0.
				uint32_t val = count > 1 ? rand() % 2 : get_bit(smooth.size(), back_matrix[i]);

				x[current] = val;

				for(int32_t u = 0; u <= i; ++u) {
					if(get_bit(current, back_matrix[u]) == 1) {
						if(val == 1)
							toggle_bit(smooth.size(), back_matrix[u]);
						unset_bit(current, back_matrix[u]);
					}
				}

				if(count == 1)
					--i;
			}
		}

		a = 1;
		b = 1;

		// The way to combine the factor base to get our square.
		memset(combination, 0, sizeof(uint32_t) * factor_base.size());
		for(uint32_t i = 0; i < smooth.size(); ++i) {
			if(x[i] == 1) {
				for(uint32_t p = 0; p < smooth[i].size(); ++p)
					++combination[smooth[i][p]];
				b *= (X[i] + sqrt_N);
			}
		}

		for(uint32_t p = 0; p < factor_base.size(); ++p) {
			for(uint32_t i = 0; i < (combination[p] / 2); ++i)
				a *= factor_base[p];
		}

		// If a = +/- b (mod N) we found a trivial factor, run the loop again to find a new a and b.
	} while(a % N == b % N || a % N == (- b) % N + N);

	b -= a;

	mpz_class factor;
	mpz_gcd(factor.get_mpz_t(), b.get_mpz_t(), N.get_mpz_t());

	for(uint32_t i = 0; i < factor_base.size(); ++i) {
		delete[] matrix[i];
		delete[] back_matrix[i];
	}

	delete[] combination;
	delete[] Y;
	delete[] fb_indexes[0];
	delete[] fb_indexes[1];
	delete[] fb_indexes;
	delete[] matrix;
	delete[] back_matrix;
	delete[] x;

	return factor;
}

int main() {
	srand(1337);

	// The primes we will perform trial division with on small integers.
	std::vector<uint32_t> primes;

	// Generate the trial division primes using a simple sieve.
	{
		uint32_t max = (uint32_t)ceil(sqrt(TRIAL_BOUND)) + 1;
		char *sieve = new char[max];
		memset(sieve, 1, max);
		for(uint32_t p = 2; p < max; ++p) {
			if(!sieve[p])
				continue;
			primes.push_back(p);
			for(uint32_t i = p; i < max; i += p)
				sieve[i] = 0;
		}
		delete[] sieve;
	}

	mpz_class N;

	// Read numbers to factor from stdin until EOF.
	while(std::cin >> N) {
		// This quadratic sieve implementation is designed to factor numbers no larger than 100 bits.
		if(mpz_sizeinbase(N.get_mpz_t(), 2) > 100) {
			std::cerr << N << " is too large\n" << std::endl;
			continue;
		}

		std::stack<mpz_class> factors;

		factors.push(N);

		while(!factors.empty()) {
			mpz_class factor = factors.top();
			factors.pop();

			// If the factor is prime, print it.
			if(mpz_probab_prime_p(factor.get_mpz_t(), 10)) {
				std::cout << factor << std::endl;
				continue;

			// Run trial division if factor is small.
			} else if(factor < TRIAL_BOUND) {
				uint32_t f = factor.get_ui();
				for(uint32_t p = 0; p < primes.size(); ++p) {
					if(f % primes[p] == 0) {
						factors.push(primes[p]);
						factors.push(factor / primes[p]);
						break;
					}
				}

			} else {
				// Before we run quadratic sieve, check for small factors.
				bool found_factor = false;
				for(uint32_t p = 0; p < primes.size(); ++p) {
					if(mpz_divisible_ui_p(factor.get_mpz_t(), primes[p])) {
						factors.push(primes[p]);
						factors.push(factor / primes[p]);
						found_factor = true;
						break;
					}
				}
				if(found_factor)
					continue;

				// Quadratic sieve doesn't handle perferct powers very well, handle those separately.
				if(mpz_perfect_power_p(factor.get_mpz_t())) {
					mpz_class root, rem;

					// Check root remainders up half of the amount of bits in factor.
					uint32_t max = mpz_sizeinbase(factor.get_mpz_t(), 2) / 2;
					for(uint32_t n = 2; n < max; ++n) {
						mpz_rootrem(root.get_mpz_t(), rem.get_mpz_t(), factor.get_mpz_t(), n);
						if(rem == 0) {
							// Push the n root factors.
							for(uint32_t i = 0; i < n; ++i)
								factors.push(root);
							break;
						}
					}

				} else {
					mpz_class f = quadratic_sieve(factor);

					factors.push(f);
					factors.push(factor / f);
				}
			}
		}

		std::cout << std::endl;
	}

	return 0;
}