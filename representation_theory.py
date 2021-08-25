import random
from itertools import product

import sage
from sage.matrix.matrix_space import MatrixSpace
from sage.rings.finite_rings.all import GF
from sage.all import matrix, vector


def equal_matrices(A, B, tol=.0001):
	return (A - B).norm('frob') < tol


def get_zero(A):
	return MatrixSpace(A.base_ring(), A.nrows(), A.ncols())(0)


def is_essentially_zero(A, tol=10**(-8)):
	return equal_matrices(get_zero(A), A, tol)


def get_identity(A):
	return MatrixSpace(A.base_ring(), A.nrows())(1)


def is_essentially_Id(matrix, tol=10**(-8)):
	return equal_matrices(get_identity(matrix), matrix, tol)


def is_plus_or_minus_Id(matrix):
	return is_essentially_Id(matrix) or is_essentially_Id(-matrix)


def is_projective_representation(matrix_list, relators):
	phi = phi_from_face_mapping(matrix_list)
	for relator in relators:
		result = phi(relator)
		if not is_plus_or_minus_Id(result):
			return False
	# print('\n{0} negative identites found'.format(negative_count))
	return True


def is_nonprojective_representation(matrix_list, relators):
	phi = phi_from_face_mapping(matrix_list)
	for relator in relators:
		if not is_essentially_Id(phi(relator)):
			return False
	return True


def is_exact_representation(matrix_list, relators):
	phi = phi_from_face_mapping(matrix_list)
	for relator in relators:
		if get_identity(matrix_list[0]) != phi(relator):
			return False
	return True


def lift_projective_SL2C_representation(matrix_list, relators):
	# phi = phi_from_face_mapping(matrix_list)
	assert is_projective_representation(matrix_list, relators)
	num_generators = int(len(matrix_list)/2)
	# base_gen_images = [phi(i+1) for i in range(int(len(matrix_list)/2))]
	pos_signs = product(*([(1, -1)] * num_generators))
	result = None
	total_iters = 2**num_generators
	iter_count = 0
	for signs in pos_signs:
		images = [None]*num_generators*2
		images[0::2] = [s * M for s, M in zip(signs, matrix_list[0::2])]
		images[1::2] = [s * M for s, M in zip(signs, matrix_list[1::2])]
		# print(signs)
		# print([str((images[i]-matrix_list[i]).norm()) for i in range(num_generators*2)])
		# gen_images = [s * M for s, M in zip(signs, base_gen_images)]
		# if not is_projective_representation(images, relators):
		# 	raise Exception('Intermediate non-representation found')
		if is_nonprojective_representation(images, relators):
			print('\nNonprojective representation found')
			result = images
			return result
		iter_count += 1
		print('\r {0:.2f}% of representations checked'.format(100*iter_count/total_iters), end='')

	if result is None:
		raise Exception('No nonprojective representation found')
	assert is_nonprojective_representation(result, relators)
	return result


def fast_lift_SL2C_representation(matrix_list, relators):
	assert is_projective_representation(matrix_list, relators)
	phi = phi_from_face_mapping(matrix_list)
	sign_vector = [0 if is_essentially_Id(phi(rel)) else 1 for rel in relators]
	Z2 = GF(2)
	sign_vector = vector(Z2, sign_vector)
	num_generators = int(len(matrix_list) / 2)
	num_relators = len(relators)
	delta = matrix(Z2, num_relators, num_generators,
			lambda i, j: relators[i].holonomy.count(j+1)-relators[i].holonomy.count(-j-1))
	if sign_vector in delta.column_space():
		z = delta.solve_right(sign_vector)
		new_matrix_list = [None]*num_generators*2
		new_matrix_list[0::2] = [(-1)**(int(z[i]))*matrix_list[2*i] for i in range(num_generators)]
		new_matrix_list[1::2] = [(-1)**(int(z[i]))*matrix_list[2*i+1] for i in range(num_generators)]
		assert is_nonprojective_representation(new_matrix_list, relators)
		return new_matrix_list
	else:
		subset = [random.randing(0, 1) for i in range(num_generators)]
		new_matrix_list = [None] * num_generators * 2
		# do the whole process again, but seeding with a different random non-projective representation
		new_matrix_list[0::2] = [(-1) ** subset[i] * matrix_list[2 * i] for i in range(num_generators)]
		new_matrix_list[1::2] = [(-1) ** subset[i] * matrix_list[2 * i + 1] for i in range(num_generators)]
		return fast_lift_SL2C_representation(new_matrix_list, relators)


# converts a number from 0 to p^4 into a matrix into a 2 by 2 matrix over Zp
def num_to_matrix(num, p):
	mat = matrix(GF(p), 2)
	mat[0, 0] = num % p
	num = num//p
	mat[0, 1] = num % p
	num = num//p
	mat[1, 0] = num % p
	num = num//p
	mat[1, 1] = num % p
	return mat


def get_SL2p_representations(group, p, return_simplified=False):
	simp = group.simplification_isomorphism()
	G = simp.codomain()
	# print(G.gens())
	Zp = GF(p)
	representations = []
	simp_representations = []
	for i in range(p**(4*G.ngens())):
		matrices = []
		for j in range(G.ngens()):
			mat = num_to_matrix(i//(p**(4*j)) % (p**4), p)
			if mat.det() != Zp.one():
				# print("bad matrix:")
				# print(mat)
				break
			else:
				matrices.append(mat)
			# print("matrices so far")
			# print(matrices)
		if len(matrices) < G.ngens():
			continue
		# print(matrices[0])
		# print(matrices[1])
		# print('\n')
		sub_dict = {str(G.gens()[i]): matrices[i] for i in range(G.ngens())}
		# print(sub_dict)
		rep = True
		for relator in G.relations():
			# print(relator.substitute(**sub_dict))
			if relator.substitute(**sub_dict) != matrix.identity(Zp, 2):
				rep = False
				break
		if rep:
			representations.append([simp(gen).substitute(**sub_dict) for gen in group.gens()])
			simp_representations.append(matrices)
	if return_simplified:
		return representations, simp_representations
	else:
		return representations


def phi_from_Tietze_mapping(mapping, identity=1):
	def phi(hol):
		if isinstance(hol, int):
			return mapping(hol)
		else:
			out = identity
			for i in hol.holonomy:
				# original
				out = out * mapping(i)
			return out
	return phi


def phi_from_face_mapping(mapping, identity=None):
	if hasattr(mapping, '__getitem__'):
		sample = mapping[0]
	else:
		sample = mapping(0)
	if identity is None:
		if isinstance(sample, sage.structure.element.Matrix):
			identity = matrix.identity(sample.base_ring(), sample.dimensions()[0])

	def t_mapping(i):
		sign = 1 if i < 0 else 0
		i = 2 * (abs(i) - 1) + sign
		if hasattr(mapping, '__getitem__'):
			return mapping[i]
		else:
			return mapping(i)

	return phi_from_Tietze_mapping(t_mapping, identity)


# snappy has the convention that the matrix corresponding to face i is the matrix which maps the opposite face to it.
def phi_from_snappy_face_mapping(mapping, identity=1):
	def t_mapping(i):
		sign = 1 if i < 0 else 0
		i = 2 * (abs(i) - 1) + sign
		if i % 2 == 0:
			i += 1
		else:
			i -= 1
		if hasattr(mapping, '__getitem__'):
			return mapping[i]
		else:
			return mapping(i)

	return phi_from_Tietze_mapping(t_mapping, identity)