import math

from sage.all import RR, vector, Combinations, ZZ, matrix

Alphabet = '$abcdefghijklmnopqrstuvwxyzZYXWVUTSRQPONMLKJIHGFEDCBA'


# Takes in a twistable domain object and determines whether edges can be removed from the dirichlet domain.
def simplifiable(tdomain):
	removable = []
	faces_by_edge = {}
	for face in tdomain.face_list:
		for edge in face.edges:
			if edge in faces_by_edge.keys():
				faces_by_edge[edge] = [faces_by_edge[edge], face]
			else:
				faces_by_edge[edge] = face
	for edge in tdomain.edges:
		face1, face2 = faces_by_edge[edge]
		if face1.opposite_edge(edge) == face2.opposite_edge(edge):
			removable.append(edge)
	return removable


class AbstractVertex(object):
	def __init__(self):
		self.adjacent_edges = []

	def __str__(self):
		return 'v{0}'.format(self.index)


class AbstractEdge(object):
	def __init__(self, tail, head):
		self.head = head
		self.tail = tail
		self.adjacent_faces = []

	def endpoints(self):
		return [self.tail, self.head]

	def other_endpoint(self, vertex):
		if vertex == self.head:
			return self.tail
		elif vertex == self.tail:
			return self.head
		else:
			raise Exception('Given vertex is not an endpoint of this cell')

	def __str__(self):
		return 'e{0}'.format(self.index)


class AbstractFace(object):
	def __init__(self, vertices=None, edges=None, edge_orientations=None):
		self.vertices = vertices
		self.edges = edges
		self.edge_orientations = edge_orientations

	def edge_sign(self, edge):
		index = self.edges.index(edge)
		return self.edge_orientations[index]

	def __str__(self):
		return 'f{0}'.format(self.index)


class AbstractPolyhedron(object):
	def __init__(self, faces=None):
		self.faces = faces


class Cell(object):
	def __init__(self, orbit=None, holonomy=None, index=None):
		self.index = index
		self.orbit = orbit
		self.holonomy = holonomy


class CellClass(object):
	def __init__(self, preferred=None, index=None, cells=None):
		if cells is None:
			cells = []
		self.index = index
		self.cells = cells
		self.preferred = preferred

	def add(self, cell):
		self.cells.append(cell)
		cell.orbit = self

	def get_reps(self):
		return self.cells

	def get_rep_indices(self):
		return [cell.index() for cell in self.cells]

	def __str__(self):
		return str(self.cells)


class Vertex(Cell, AbstractVertex):
	def __init__(self, orbit=None, holonomy=None, index=None, coords=None):
		Cell.__init__(self, orbit, holonomy, index)
		AbstractVertex.__init__(self)
		if coords is not None:
			self.set_coords(coords)
		else:
			self.coords = None

	def __str__(self):
		return '{0}(V{1})'.format(self.holonomy.holonomy, str(self.orbit.index))

	def __hash__(self):
		if self.index is None:
			return hash(self.holonomy)
		else:
			return hash(self.holonomy)*self.index

	def set_coords(self, coords):
		self.coords = vector([1, 0, 0, 0], RR)
		for i in range(3):
			self.coords[i+1] = float(coords[i])
		self.coords = self.coords / math.sqrt(abs(1 - sum(self.coords[i] ** 2 for i in range(1, 4))))

	# Returns the coordinates obtained by applying the holonomy on the coordinates of the preferred vertex
	def coords_from_holonomy(self):
		return self.holonomy.matrix()*self.orbit.preferred.coords


class VertexOrbit(CellClass, AbstractVertex):
	def __init__(self, preferred=None, index=None, cells=None):
		CellClass.__init__(self, preferred, index, cells)
		AbstractVertex.__init__(self)

	def __str__(self):
		return 'V{0}'.format(self.index)


class Edge(AbstractEdge, Cell):
	def __init__(self, orbit=None, holonomy=None, tail=None, head=None, index=None):
		Cell.__init__(self, orbit, holonomy, index)
		AbstractEdge.__init__(self, tail, head)

	def __str__(self):
		return '{0}(E{1})'.format(self.holonomy.holonomy, str(self.orbit.index))

	def __hash__(self):
		return hash(self.head) * hash(self.tail) * hash(self.holonomy)


class EdgeOrbit(CellClass, AbstractEdge):
	def __init__(self, preferred=None, tail=None, head=None, index=None):
		CellClass.__init__(self, preferred, index)
		AbstractEdge.__init__(self, tail, head)

	# Returns the lift of this edge which starts at the given vertex.
	# if head or tail is True (if both are true, this will throw an error)
	# this will check to make sure that the given lift will have its head or tail at the
	# specified vertex.
	# If neither is specified, this will make sure that one of them is
	# (and will print a warning if both are of them are, as the lift will not be unique
	# in this case, it will give the lift from the tail)
	def lift(self, vertex, head=None, tail=None):
		assert not (head and tail)
		if head is None and tail is None:
			assert vertex.orbit in [self.head, self.tail]
			if vertex.orbit == self.head and vertex.orbit == self.tail:
				print(
					'Warning: Given edge is a loop and head or tail not specified. Lift will not be unique, '
					'tail is chosen')
				tail = True
			if vertex.orbit == self.head:
				head = True
			elif vertex.orbit == self.tail:
				tail = True
		edge = self.preferred
		if tail:
			assert self.tail == vertex.orbit
			to_initial = edge.tail.holonomy.inverse()
		elif head:
			assert self.head == vertex.orbit
			to_initial = edge.head.holonomy.inverse()
		else:
			raise Exception('Should not have reached here')
		edge = to_initial.apply(edge)
		return vertex.holonomy.apply(edge)

	def __str__(self):
		return 'E{0}'.format(self.index)


class Face(Cell, AbstractFace):
	def __init__(self, orbit=None, holonomy=None, vertices=None, edges=None, paired_vertices=None, paired_edges=None,
				edge_orientations=None, index=None, paired_face=None):
		Cell.__init__(self, orbit, holonomy, index)
		AbstractFace.__init__(self, vertices, edges, edge_orientations)
		self.paired_vertices = paired_vertices
		self.paired_edges = paired_edges
		self.paired_face = paired_face

	def opposite_face(self):
		return self.paired_face

	def opposite_vertex(self, vertex):
		index = self.vertices.index(vertex)
		return self.paired_vertices[index]

	def opposite_edge(self, edge):
		index = self.edges.index(edge)
		return self.paired_edges[index]

	def get_Tietze(self):
		sign = -1 if self.index % 2 == 1 else 1
		return math.floor(self.index / 2) * sign

	def get_letter(self):
		if abs(self.index) > 26:
			raise Exception('Face index too high to get letter')
		return Alphabet[self.get_Tietze()]


class FaceOrbit(CellClass, AbstractFace):
	def __init__(self, preferred=None, vertices=None, edges=None, signs=None, index=None):
		CellClass.__init__(self, preferred, index)
		AbstractFace.__init__(self, vertices, edges, signs)


class Simplex:
	"""
	A class which represents a simplex in a triangulation of a manifold.
	In this case, we define a simplex by its faces as opposed to vertices so that the triangulation can represent delta
	complexes as opposed to pure simplicial complexes.
	"""
	def __init__(self, index, faces, face_orientations, data=None):
		self.index = index
		self.faces = faces
		self.dim = len(faces)
		self.face_orientations = face_orientations
		self.data = data

	def dimension(self):
		return self.dim

	def boundary(self, n=None):
		"""
		Returns a list of all of the n-dimensional cells which are faces of this one. If n is None, this returns the
		boundary faces of this simplex
		"""
		assert self.dim >= n
		if n is None:
			n = self.dim - 1
		if n == self.dim:
			return {self}
		if n == self.dim - 1:
			return self.faces
		return set().union(*[face.boundary(n) for face in self.faces])

	def is_zero_simplex(self):
		return False

	def __hash__(self):
		return self.dimension()**self.index


class ZeroSimplex(Simplex):
	def __init__(self, index, coords=None, data=None):
		Simplex.__init__(self, index, faces=[], face_orientations=[], data=data)
		self.coords = coords

	def is_zero_simplex(self):
		return True

	def __hash__(self):
		return self.index


class Triangulation:
	"""
	A class for organizing simplices in a triangulation. (Note that this is not a simplicial complex because two
	different simplices may have the same vertices)
	"""

	def __init__(self, vertices=None):
		self.simplices = dict()
		if vertices is not None:
			if isinstance(vertices, int):
				self.simplices[0] = [ZeroSimplex(i) for i in range(vertices)]
			elif isinstance(vertices, list):
				self.simplices[0] = [ZeroSimplex(i, coords) for i, coords in enumerate(vertices)]
		else:
			self.simplices[0] = []

	def add_new_vertices(self, num, data=None):
		"""
		Adds num new vertices to this triangulation and returns them to the user
		"""
		if data is None:
			data = [None]*num
		new_vertices = [ZeroSimplex(len(self.simplices[0]) + i, data[i]) for i in range(num)]
		self.simplices[0].extend(new_vertices)
		return new_vertices

	def add_new_vertex(self, data=None):
		return self.add_new_vertices(1, [data])

	def add_new_simplex(self, faces, orientations, data=None):
		dim = len(faces) - 1
		if dim not in self.simplices.keys():
			self.simplices[dim] = []
		for face in faces:
			assert face in self.simplices[dim-1]
		assert len(faces) == len(orientations)
		new_simplex = Simplex(len(self.simplices[dim]), faces, orientations, data)
		self.simplices[dim].append(new_simplex)
		return new_simplex

	def add_new_simplices(self, faces_list, orientations_list, data=None):
		if data is None:
			data = [None]*len(faces_list)
		new_simplices = []

		for faces, orientations, datum in zip(faces_list, orientations_list, data):
			new_simplices.append(self.add_new_simplex(faces, orientations, datum))
		return new_simplices

	def get_boundary_map(self, n):
		"""
			Returns the boundary map of this delta complex going from C_{n} to C_{n-1}.
		"""
		C_n_size = len(self.simplices[n])
		C_n_minus1_size = len(self.simplices[n-1])
		# if C_n_size or C_nplus1_size
		boundary_matrix = matrix(ZZ, C_n_minus1_size, C_n_size)
		# print(C_n_size, C_n_minus1_size)
		# print(boundary_matrix)
		for simplex in self.simplices[n]:
			# print(simplex.face_orientations)
			for face, orientation in zip(simplex.faces, simplex.face_orientations):
				boundary_matrix[face.index, simplex.index] += orientation
		return boundary_matrix




