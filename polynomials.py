from sage.all import PolynomialRing, LaurentPolynomialRing
from sage.all import ZZ, CC, RR
from sage.all import vector
from sage.all import matrix
from functools import reduce

# This file is a substitute for the sagemath singular interface (which doesn't work with complex numbers)
# All polynomials here are assumed to be multivariate polynomials unless otherwise specified.


def clean_polynomial_matrix(mat, eps=10**(-15)):
	new_mat = matrix(mat.base_ring(), mat.nrows(), mat.ncols(), 0)
	for i in range(mat.nrows()):
		for j in range(mat.ncols()):
			new_mat[i, j] = clean_polynomial(mat[i, j], eps)
	return new_mat


def clean_polynomial(poly, eps=10**(-15)):
	def clean_coefficient(coeff):
		ring = poly.base_ring()
		matches = [ring(0), -ring(1), ring(1)]
		for num in matches:
			if (coeff - num).abs() < eps:
				return num
		return coeff
	return poly.map_coefficients(clean_coefficient)


# returns a  list of the terms which make up the polynomial.
# why doesn't sage already have this???
def terms_list(poly):
	return [a*b for a, b in zip(poly.coefficients(), poly.monomials())]


# given a laurent polynomial, returns the minimum exponent of every variable over all the terms
# e.g. xy + x^2z + xy^-1 -> (1, -1, 0)
def min_exponent_tuple(poly):
	exps = poly.exponents()
	comp = lambda x, y: [min(x[i], y[i]) for i in range(len(x))]
	if len(exps) == 0:
		return [0]*poly.parent().ngens()
	elif len(exps) == 1:
		return exps[0]
	min_exps = reduce(comp, exps)
	return min_exps


def max_exponent_tuple(poly):
	exps = poly.exponents()
	comp = lambda x, y: [max(x[i], y[i]) for i in range(len(x))]
	if len(exps) == 0:
		return [0] * poly.parent().ngens()
	elif len(exps) == 1:
		return exps[0]
	min_exps = reduce(comp, exps)
	return min_exps


def laurent_matrix_to_poly_matrix(mat):
	min_exp_list = [min_exponent_tuple(poly) for poly in mat.list()]
	poly_ring = mat.base_ring()
	comp = lambda x, y: [min(x[i], y[i]) for i in range(len(x))]
	min_exps = reduce(comp, min_exp_list, [0]*poly_ring.ngens())
	mat = mat*(exponent_vec_to_monomial([-x for x in min_exps], poly_ring.gens()))
	new_mat = matrix(poly_ring.polynomial_ring(), [[simple_laurent_to_poly(mat[j, i]) for i in range(mat.dimensions()[0])]
																					for j in range(mat.dimensions()[1])])
	return new_mat


# You should only use this when you know that your Laurent polynomial actually is a polynomial
def simple_laurent_to_poly(laurent):
	if min(min_exponent_tuple(laurent)) < 0:
		raise Exception('Cannot simply convert laurent polynomial to polynomial')
	return sum([a * b for a, b in zip(laurent.coefficients(), [exponent_vec_to_monomial(exp,
					laurent.parent().polynomial_ring().gens()) for exp in laurent.exponents()])])


def laurent_to_poly(laurent):
	laurRing = laurent.parent()
	polyRing = PolynomialRing(laurRing.base_ring(), laurRing.ngens(), laurRing.variable_names())
	exponents = laurent.exponents()
	exponents = list(zip(*exponents))
	m = vector(ZZ, ([min(exp_list) for exp_list in exponents]))
	exponents = [vector(ZZ, vec) for vec in laurent.exponents()]
	assert sum([a * b for a, b in zip(laurent.coefficients(), [exponent_vec_to_monomial(exp, polyRing.gens()) for exp in
															exponents])]) == laurent
	return sum(
		[a * exponent_vec_to_monomial(n - m, polyRing.gens()) for a, n in zip(laurent.coefficients(), exponents)],
		polyRing(0))


def exponent_vec_to_monomial(vec, gens):
	result = gens[0].parent()(1)
	for i, exp in enumerate(vec):
		result = result * gens[i] ** exp
	return result


# in graded reverse lexicographical order (grevlex)
def monomial_less_than(mon1, mon2):
	deg1, deg2 = vector(ZZ, mon1.degrees()), vector(ZZ, mon2.degrees())
	diff = deg2 - deg1
	sign = [x for x in diff if x != 0][-1]  # gets the rightmost non-zero entry
	return sign > 0


def leading_term(poly):
	terms = terms_list(poly)
	if len(terms) == 0:
		return poly
	# def comp(mon1, mon2):
	# 	return mon2 if monomial_less_than(mon1, mon2) else mon1
	comp = lambda mon1, mon2: mon2 if monomial_less_than(mon1, mon2) else mon1
	lt = reduce(comp, terms)
	return lt


# assumes that mon1 is divisible by mon2 and returns mon1/mon2
def monomial_quotient(mon1, mon2):
	exp1, exp2 = vector(ZZ, mon1.degrees()), vector(ZZ, mon2.degrees())
	exp = exp1 - exp2
	coeff = mon1.coefficients()[0]/mon2.coefficients()[0]
	return coeff*exponent_vec_to_monomial(exp, mon1.parent().gens())


def factor_out_monomial(poly):
	if poly.parent().ngens() == 1:
		poly = PolynomialRing(poly.base_ring(), 1, poly.parent().gen())(poly)
	factor = exponent_vec_to_monomial(min_exponent_tuple(poly), poly.parent().gens())
	factor_vec = vector(ZZ, min_exponent_tuple(poly))
	new_poly = sum([coeff * exponent_vec_to_monomial(exp-factor_vec, poly.parent().gens()) for coeff, exp in
									zip(poly.coefficients(), [vector(ZZ, tup) for tup in poly.exponents()])])
	if poly.parent().ngens() == 1:
		uniPolyRing = PolynomialRing(poly.base_ring(), poly.parent().gen())
		new_poly, factor = uniPolyRing(new_poly), uniPolyRing(factor)
	return new_poly, factor


# returns True if mon1 divides mon2
def divides(mon1, mon2):
	exp1, exp2 = mon1.degrees(), mon2.degrees()
	assert len(exp1) == len(exp2)
	for i in range(len(exp1)):
		if exp1[i] > exp2[i]:
			return False
	return True


# assumes the denominator has no common factor and is not a monomial
def quo_rem(numerator, denominator):
	remainder = quotient = numerator.parent()(0)
	numerator, numerator_common_factor = factor_out_monomial(numerator)
	while numerator != 0:
		print('remaining numerator: %s' % numerator)
		while divides(leading_term(denominator), (leading_term(numerator))):
			print('leading_term of numerator: %s' % leading_term(numerator))
			multiplier = monomial_quotient(leading_term(numerator), leading_term(denominator))
			quotient = quotient + multiplier
			numerator = numerator - multiplier*denominator
		lt = leading_term(numerator)
		remainder = remainder + lt
		numerator = numerator - lt
	return quotient*numerator_common_factor, remainder*numerator_common_factor


def symmetrize_polynomial(poly):
	"""
	Given a possibly multivariate polynomial which is symmetrizable (it is symmetric up to multiplying by a
	monomial), returns the truly symmetrized version
	"""
	if poly.parent().ngens() == 1:
		poly = PolynomialRing(poly.base_ring(), 1, poly.parent().gen())(poly)
	two_exponent_tuple = (a-b for (a, b) in zip(max_exponent_tuple(poly), min_exponent_tuple(poly)))
	exponent_tuple = vector(ZZ, [num/2 for num in two_exponent_tuple])
	print(exponent_tuple)
	factor_vec = vector(ZZ, exponent_tuple)
	new_poly = sum([coeff * exponent_vec_to_monomial(exp-factor_vec, poly.parent().gens()) for coeff, exp in
									zip(poly.coefficients(), [vector(ZZ, tup) for tup in poly.exponents()])])
	if poly.parent().ngens() == 1:
		uniPolyRing = PolynomialRing(poly.base_ring(), poly.parent().gen())
		new_poly= uniPolyRing(new_poly)
	return new_poly


def bezout_coeffs(vec):
	"""
		Given a vector with entries which have a xgcd function, returns bezout coefficients for the entire vector
	"""
	coeffs = [0] * len(vec)
	gcd = 0
	total_gcd = vec
	i = 0
	while gcd != total_gcd:
		gcd, coeff1, coeff2 = xgcd(gcd, vec[i])
		for j in range(i):
			coeffs[l] *= coeff1
		coeffs[i] = coeff2
		i += 1
	assert sum([coeffs[i] * vec[i] for i in range(len(vec))]) == total_gcd
	return coeffs


def single_division_test(num, den):
	print('\nNew Test')
	print('numerator:{0}'.format(num))
	print('denominator:{0}'.format(den))
	quorem = quo_rem(num, den)
	print('quotient:{0}'.format(quorem[0]))
	print('remainder:{0}'.format(quorem[1]))
	print('the next two lines should be roughly equal')
	print(num)
	print(den*quorem[0]+quorem[1])


def test_matrix_conversion():
	ring = LaurentPolynomialRing(CC, 3, 'xyz')
	generators = ring.gens()
	x, y, z = generators[0], generators[1], generators[2]
	mat = matrix(ring, [[z*x**(-i)*y**(-j) for i in range(3)] for j in range(3)])
	other_mat = matrix(ring, [[x]])
	print(mat)
	print(laurent_matrix_to_poly_matrix(mat))


def test_division():
	ring = PolynomialRing(CC, 3, 'xyz')
	generators = ring.gens()
	x, y, z = generators[0], generators[1], generators[2]

	num = 3 * x ** 2 * y + 2 * x ** 2 + 3 * y
	den = x * y
	single_division_test(num, den)

	num = x*(y+z)
	den = y+z
	single_division_test(num, den)

	num = x * (y + z)
	den = .9999999999999999999*y + 1.0000000000001*z
	single_division_test(num, den)


if __name__ == "__main__":
	test_matrix_conversion()

