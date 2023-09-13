#! /data/keeling/a/nmd/miniconda3/envs/sage_full/bin/sage-python -u
#
#SBATCH --partition m
#SBATCH --tasks=1
#SBATCH --mem-per-cpu=4G
#SBATCH --nice=10000
#SBATCH --time=7-00:00
#SBATCH --array=0-19
#SBATCH --output=/data/keeling/a/jdm7/slurm_out/zero_filled_cusps_%a
#SBATCH --error=/data/keeling/a/jdm7/slurm_error/zero_filled_cusps_error_%a
import time

import snappy
import sys, os
from sage.all import CyclotomicField, PolynomialRing, pi, golden_ratio, exp, copy
sys.path.append('./..')
import twistable_revamp
import pickle
import pandas as pd


def approximate_polynomial(M, tol = .0001, bound = None, method = None):
	S0, S1, S2 = [normalize_matrix(S) for S in get_matrices(M)]
	C = S0.base_ring().base_ring()
	if bound is None:
		# improve this
		deg_bound1 = S1.dimensions()[0]*max(poly.degree() for poly in S1)
		deg_bound2 = min(poly.degree() for poly in S0) + min(poly.degree() for poly in S2)
		bound = deg_bound1 - deg_bound2

	if method is None:
		method = 0
	if method == 'roots_of_unity' or method == 0:
		gen = CyclotomicField().gen(bound)
		inputs = [gen**i for i in range(bound)]
	elif method == 'golden_angle':
		inputs = [exp(i*C.gen()*2*pi/(golden_ratio**2)) for i in range(bound)]
	elif method == 'random_unit_square':
		inputs = []
		while len(inputs) < bound:
			num = C.random_element()
			if num.abs() <= 1:
				inputs.append(num)

	P = PolynomialRing(C, 't')

	outputs_full = [S1(C(num)).determinant()/(S0(C(num)).determinant()*S2(C(num)).determinant()) for num in inputs]
	# outputs_top = [S1(C(num)).determinant() for num in inputs]
	# denominator = (S0.determinant() * S1.determinant())(P.gen())

	points_full = zip(inputs, outputs_full)
	# points_top = zip(inputs, outputs_top)

	poly = P.lagrange_polynomial(points_full)
	# poly_top = P.lagrange_polynomial(points_top)
	# print(poly_top.quo_rem(denominator))
	#print(poly, '\n')
	clean_poly = clean_polynomial(poly, tol)
	# clean_bottom = normalize_polynomial(denominator.map_coefficients(clean))
	# clean_top = normalize_polynomial(poly_top.map_coefficients(clean))
	# print(clean_top.quo_rem(clean_bottom))
	return normalize_polynomial(clean_poly)


def repeated_approximation(M, bounds, method=None):
	test_bound = 2*max(bounds)
	S0, S1, S2 = get_matrices(M)
	C = S0.base_ring().base_ring()
	# inputs = [C.random_element() for _ in range(test_bound)]
	# outputs = [S1(C(num)).determinant() / (S0(C(num)).determinant() * S2(C(num)).determinant()) for num in inputs]
	for bound in bounds:
		poly = approximate_polynomial(M, bound=bound, method=method)
		# test_outputs = [poly(C(num)) for num in inputs]
		print(bound)
		print(poly)
		# print(max([(test_outputs[i] - outputs[i]).abs() for i in range(len(inputs))]))
		print()

def get_matrices(M, hp = False):
	assert M.homology().betti_number() > 0
	# M = M.high_precision()
	D = M.dirichlet_domain()
	DD = twistable_revamp.TwistableDomain(D)
	return DD.torsion_polynomial(return_matrices=True)

def normalize_polynomial(poly):
	monomial = poly.parent().gen()**(min(poly.exponents()))
	return poly.quo_rem(monomial)[0]

def apply_points(Si, inputs, normalize=False, eps = None):
	S0, S1, S2 = Si
	C = S0.base_ring().base_ring()
	if eps is None:
		eps = C.epsilon()
	t = S0.base_ring().gen()
	# if normalize, multiply the denominator by t enough times so that we have a non-zero constant term
	if normalize:
		S0 = S0*S0.matrix_space().identity_matrix()
		i = 0
		while S1(eps).det()/(S0(eps).det()*S2(eps).det()) < eps:
			S0[0,:] = t*S0[0,:]
			i += 1
			if i > 10000:
				print('number of iterations exceeded 10000')
	return [S1(C(num)).determinant() / (S0(C(num)).determinant() * S2(C(num)).determinant()) for num in inputs]


def normalize_matrix(M):
	M = copy(M)
	if hasattr(M.base_ring(), 'univariate_ring'):
		M = univariate_matrix(M)
	P = M.base_ring()
	t = P.gen()
	for i in range(M.dimensions()[0]):
		entries = M[i,:].list()
		max_exp = max([entry.degree() for entry in entries])
		min_exp  = max_exp
		for entry in entries:
			min_exp = min(min_exp, min(entry.exponents(), default = max_exp))
		entries = [[entry.quo_rem(t**min_exp)[0] for entry in entries]]
		M[i,:] = entries
	for i in range(M.dimensions()[1]):
		entries = M[:,i].list()
		max_exp = max([entry.degree() for entry in entries])
		min_exp  = max_exp
		for entry in entries:
			min_exp = min(min_exp, min(entry.exponents(), default = max_exp))
		entries = [[entry.quo_rem(t**min_exp)[0]] for entry in entries]
		M[:,i] = entries
	return M

def univariate_matrix(M):
	P = M.base_ring()
	assert P.ngens() == 1
	M = M.change_ring(P.univariate_ring(P.variable_name()))
	return M


def clean_polynomial(p, tol = .0001):
	C = p.base_ring()
	def clean(num):
		exacts = [C(i) for i in range(-2,3)]
		for exact in exacts:
			if (num.imag() - C(exact)).abs() < tol:
				num = num.real() + exact*C.gen()
				break
		for exact in exacts:
			if (num.real() - C(exact)).abs() < tol:
				num = exact + num.imag()*C.gen()
				break
		return num

	return p.map_coefficients(clean)

def main(index = None, tol = None):
	if index is None:
		index = 0

	M = snappy.OrientableClosedCensus(betti = 1)[index].high_precision()
	Si = get_matrices(M)
	S0, S1, S2 = Si
	C = S0.base_ring().base_ring()
	if tol is None:
		tol = C(2**(-S0.base_ring().base_ring().precision()/2))
	Si = [normalize_matrix(S) for S in Si]
	for S in Si:
		for i in range(S.dimensions()[0]):
			for j in range(S.dimensions()[1]):
				S[i, j] = clean_polynomial(S[i, j], tol=tol)
	tol = tol.sqrt().sqrt().sqrt()
	num_clean = clean_polynomial(S1.det(), tol)
	num_clean = normalize_polynomial(num_clean)
	print(num_clean)
	den_clean = clean_polynomial(S0.det()*S2.det(), tol)
	den_clean = normalize_polynomial(den_clean)
	quo, rem = num_clean.quo_rem(den_clean)
	tol = tol.sqrt()
	quo = clean_polynomial(quo, tol)
	rem = clean_polynomial(rem, tol)

	print()
	print('quo', quo)
	print()
	print('rem', rem)
	return quo, rem, Si, (num_clean, den_clean)

def main2(index=None):
	M = snappy.OrientableClosedCensus(betti=1)[index].high_precision()
	# repeated_approximation(M, range(4, 25))
	repeated_approximation(M, range(4, 25), method='golden_angle')

def main3():
	for i, M in enumerate(snappy.OrientableClosedCensus(betti = 1)):
		M = M.high_precision()
		poly = approximate_polynomial(M, tol = .00000001, method='golden_angle')
		coeffs = poly.coefficients()
		for j in range(len(coeffs)):
			if (coeffs[j] - coeffs[-j-1]).abs() > .0001:
				print(f'{j} coefficient of manifold {i} not symmetric')
		with open('/data/keeling/a/jdm7/torsion_poly_out/torsion_poly_%i' % i, 'wb') as file:
			pickle.dump(poly, file)

def main4():
	data = pd.read_csv('/data/keeling/a/jdm7/torsion/data_for_joseph.csv')

	num_jobs = 20
	task = int(os.environ['SLURM_ARRAY_TASK_ID'])

	for name in data['name'][task::num_jobs]:
		if f'{name}_output' in os.listdir():
			continue
		M = snappy.Manifold(name)
		M = M.high_precision()
		if M.num_cusps() != 1:
			continue
		longitude = M.homological_longitude()
		if longitude is None:
			continue
		M.dehn_fill(longitude)
		if M.solution_type(enum = True) > 1 or M.volume() < .5:
			continue
		if M.homology().betti_number() != 1:
			continue
		# if M.alexander_polynomial().degree() > 1:
		# 	continue
		tic = time.perf_counter()
		poly = approximate_polynomial(M, tol = .00000001, method='golden_angle')
		elapsed = time.perf_counter() - tic
		out = {'poly': poly, 'time':elapsed}
		coeffs = poly.coefficients()
		for j in range(len(coeffs)):
			if (coeffs[j] - coeffs[-j-1]).abs() > .0001:
				print(f'{j} coefficient of manifold {name} not symmetric')
		with open(f'/data/keeling/a/jdm7/zero_filled_cusps/{name}_output_triv_alex', 'wb') as file:
			pickle.dump(out, file)

if __name__ == '__main__':
	main4()
