from sage.all import matrix, RR, CC, I, vector, pi, RealField
import random
import math

# Something in this is brokem, but the O31_to_Moebius converter seems to work fine


# Takes a vector in R3 and adds a time coordinate so that it becomes a valid point in R(3,1)
# under the convention that the time coordinate comes first
def add_time_coordinate_first(coords):
	new_coords = vector([1, 0, 0, 0], RR)
	for i in range(3):
		new_coords[i+1] = float(coords[i])
	new_coords = new_coords / math.sqrt(abs(1 - sum(new_coords[i] ** 2 for i in range(1, 4))))
	return new_coords


# converts a snappy O31 matrix to a moebius transformation (i.e. a matrix) in SL(2,C)
def O31_to_Moebius(mat, precision=53):
	# algorithm basically copied line-for-line from the snap kernel source code
	R = RealField(precision)
	B = matrix(R, mat)
	if B.determinant() < 0:
		B = -B
	A = matrix(CC, 2, 2)
	AM0A_00 = B[0, 0] + B[1, 0]
	AM1A_00 = B[0, 1] + B[1, 1]
	aa = AM0A_00 + AM1A_00
	bb = AM0A_00 - AM1A_00
	if aa > bb:
		A[0, 0] = aa + 0*I
		A[0, 1] = B[0, 2] + B[1, 2] + (B[0, 3] + B[1, 3])*I
		A[1, 0] = B[2, 0] + B[2, 1] - (B[3, 0] + B[3, 1])*I
		A[1, 1] = B[2, 2] + B[3, 3] + (B[2, 3] - B[3, 2])*I
	else:
		A[0, 0] = B[0, 2] + B[1, 2] - (B[0, 3] + B[1, 3])*I
		A[0, 1] = bb + 0*I
		A[1, 0] = B[2, 2] - B[3, 3] - (B[2, 3] + B[3, 2])*I
		A[1, 1] = B[2, 0] - B[2, 1] + (B[3, 1] - B[3, 0])*I
	A = A/A.determinant().sqrt()
	return A


def apply_Moebius_transformation(transformation, point):
	a = transformation[0, 0]
	b = transformation[0, 1]
	c = transformation[1, 0]
	d = transformation[1, 1]
	z = point[0] + point[1]*I
	t = point[2]
	denom = (c*z+d).abs()**2+(t*c).abs()**2
	# print(a, b, c, d, z, t)
	# print('denom')
	# print(denom)
	z_prime = ((a*z+b)*(c*z+d).conjugate()+a*c.conjugate()*t**2)/denom
	# print('z_prime')
	# print(z_prime)
	t_prime = t/denom
	z_prime = CC(z_prime)
	return vector(RR, [z_prime.real(), z_prime.imag(), t_prime])


def hyperboloid_point_to_Poincare_ball(x):
	x = vector(x)
	return x[1:]/(1 + x[0])


def Poincare_ball_point_to_hyperboloid(x):
	x = vector(x)
	y = vector(RR, 4)
	y[1:4] = 2*x
	x_squared = x.dot_product(x)
	y[0] = 1 + x_squared
	y = y/(1 - x_squared)
	return y


def Poincare_ball_point_to_upper_half(x):
	x = vector(x)
	e_3 = vector(RR, [0, 0, 1])
	denom = (x + e_3).dot_product(x + e_3)
	y = 2*(x + e_3)/denom - e_3
	return y


def upper_half_point_to_Poincare_ball(x):
	# This function is its own inverse
	return Poincare_ball_point_to_upper_half(x)


def hyperboloid_point_to_upper_half(x):
	y = Poincare_ball_point_to_upper_half(hyperboloid_point_to_Poincare_ball(x))
	return y


def upper_half_point_to_hyperboloid_point(x):
	y = Poincare_ball_point_to_hyperboloid(upper_half_point_to_Poincare_ball(x))
	return y


def arbitrary_point_in_hyperboloid():
	x = vector(RR, [RR.random_element(-1, 1), RR.random_element(-1, 1), RR.random_element(-1, 1)])
	x = x / math.sqrt(x.dot_product(x))
	size = RR.random_element(0, 1)
	x = size * x
	x = add_time_coordinate_first(x)
	return x


def test_isomorphism():
	lorentz1 = random.choice(random.choice(snappy.OrientableClosedCensus).dirichlet_domain().pairing_matrices())
	lorentz2 = random.choice(random.choice(snappy.OrientableClosedCensus).dirichlet_domain().pairing_matrices())
	print('One of the following matrices should be 0 (due to the fact that the lift to SL(2,C) is not unique)')
	A = O31_to_Moebius(lorentz1)*O31_to_Moebius(lorentz2)
	B = O31_to_Moebius(lorentz1*lorentz2)
	print(A+B)
	print(A-B)


def test_model_conversions():
	x = vector(RR, [0, 0, -.5])
	x = add_time_coordinate_first(x)
	print('original point in hyperboloid model')
	print(x)
	print('checking to make sure that the form applied to the point gives -1')
	print(-(x[0]**2) + sum([x[i]**2 for i in range(1, 4)]))
	x_prime = hyperboloid_point_to_Poincare_ball(x)
	print('point mapped to ball model')
	print(x_prime)
	print('point mapped to upper half model')
	y = Poincare_ball_point_to_upper_half(x_prime)
	assert (y-hyperboloid_point_to_upper_half(x)).norm() < .0001
	print(y)
	print(upper_half_point_to_hyperboloid_point(hyperboloid_point_to_upper_half(x)))


def test_Moebius_application():
	x = vector(RR, [0, 0, 1])
	A = matrix.identity(CC, 2)
	A[0, 1] = 2+4*I
	print(apply_Moebius_transformation(A, x))
	B = matrix(CC, 2, 2, [math.sqrt(2), 0, 0, 1/math.sqrt(2)])
	print(apply_Moebius_transformation(B, x))
	print(apply_Moebius_transformation(A, apply_Moebius_transformation(B, x)))
	print(apply_Moebius_transformation(A*B, x))


def test_diagram_commutativity():
	print('The following should be roughly [0,0,1]')
	print(hyperboloid_point_to_upper_half([1, 0, 0, 0]))

	x = arbitrary_point_in_hyperboloid()
	print('random vector in hyperboloid model')
	print(x)
	lorentz_matrix = random.choice(random.choice(snappy.OrientableClosedCensus).dirichlet_domain().pairing_matrices())
	print('Lorentz matrix')
	print(lorentz_matrix)
	moebius = O31_to_Moebius(lorentz_matrix)
	print('Moebius transformation matrix')
	print(moebius)
	x_prime = hyperboloid_point_to_upper_half(x)
	print('corresponding point in upper half space')
	print(x_prime)
	print(apply_Moebius_transformation(moebius, x_prime))
	print(hyperboloid_point_to_upper_half(lorentz_matrix*x))


def test_conversion():
	manifold = random.choice(snappy.OrientableClosedCensus)
	group = manifold.fundamental_group()
	gens = group.generators()
	word = random.choice(gens)
	lorentz = group.O31(word)
	converted_moebius = O31_to_Moebius(lorentz)
	snappy_moebius = group.SL2C(word)
	print('One of these numbers should be about 0')
	print((snappy_moebius-converted_moebius).norm())
	print((snappy_moebius+converted_moebius).norm())


if __name__ == '__main__':
	import snappy
	test_conversion()
