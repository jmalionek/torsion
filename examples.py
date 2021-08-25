import snappy
import numpy
import spherogram


class ThreeTorusStructue:
	def __init__(self):
		self.faces = []
		self.edges = []
		self.vertices = []
		self.set_up_faces()
		self.set_up_edges()
		self.set_up_vertices()

	# noinspection PyDictCreation
	def set_up_faces(self):
		f0 = {}
		f0['vertex_indices'] = [0, 2, 6, 4]
		f0['vertex_image_indices'] = [1, 3, 7, 5]
		f0['edge_indices'] = [0, 10, 3, 1]
		f0['edge_image_indices'] = [9, 7, 6, 4]
		f0['edge_orientations'] = [1, 1, -1, -1]
		f1 = {}
		f1['vertex_indices'] = [1, 5, 7, 3]
		f1['vertex_image_indices'] = [0, 4, 6, 2]
		f1['edge_indices'] = [4, 6, 7, 9]
		f1['edge_image_indices'] = [1, 3, 10, 0]
		f1['edge_orientations'] = [1, 1, -1, -1]
		f2 = {}
		f2['vertex_indices'] = [0, 1, 3, 2]
		f2['vertex_image_indices'] = [4, 5, 7, 6]
		f2['edge_indices'] = [2, 9, 11, 0]
		f2['edge_image_indices'] = [5, 6, 8, 3]
		f2['edge_orientations'] = [1, 1, -1, -1]
		f3 = {}
		f3['vertex_indices'] = [4, 6, 7, 5]
		f3['vertex_image_indices'] = [0, 2, 3, 1]
		f3['edge_indices'] = [3, 8, 6, 5]
		f3['edge_image_indices'] = [0, 11, 9, 2]
		f3['edge_orientations'] = [1, 1, -1, -1]
		f4 = {}
		f4['vertex_indices'] = [0, 4, 5, 1]
		f4['vertex_image_indices'] = [2, 6, 7, 3]
		f4['edge_indices'] = [1, 5, 4, 2]
		f4['edge_image_indices'] = [10, 8, 7, 11]
		f4['edge_orientations'] = [1, 1, -1, -1]
		f5 = {}
		f5['vertex_indices'] = [2, 3, 7, 6]
		f5['vertex_image_indices'] = [0, 1, 5, 4]
		f5['edge_indices'] = [11, 7, 8, 10]
		f5['edge_image_indices'] = [2, 4, 5, 1]
		f5['edge_orientations'] = [1, 1, -1, -1]
		self.faces = [f0, f1, f2, f3, f4, f5]

	def set_up_vertices(self):
		for i in range(8):
			self.vertices.append({'vertex_class': 0})

	def set_up_edges(self):
		classes = [0, 1, 2] * 4
		tails = [0, 0, 0, 4, 1, 4, 5, 3, 6, 1, 2, 2]
		tips = [2, 4, 1, 6, 5, 5, 7, 7, 7, 3, 6, 3]
		for i in range(12):
			d = {'edge_class': classes[i], 'tip_vertex_index': tips[i], 'tail_vertex_index': tails[i]}
			self.edges.append(d)

	# noinspection PyUnusedLocal
	def vertex_list(self, param=True):
		return self.vertices

	def face_list(self):
		return self.faces

	def edge_list(self):
		return self.edges


class SeifertWeberStructure:
	def __init__(self):
		self.vertices = [{'vertex_class': 0}] * 20
		self.edges = []
		self.faces = []
		self.set_up_faces()
		self.set_up_edges()

	def set_up_edges(self):
		classes = [0, 1, 2, 3, 4] * 5 + [5] * 5
		tails = mod_5_range(0) + mod_5_range(16) + mod_5_range(18) + mod_5_range(9) + mod_5_range(6) + mod_5_range(10)
		tips = mod_5_range(1) + mod_5_range(17) + mod_5_range(13) + mod_5_range(4) + mod_5_range(11) + mod_5_range(6)
		for i in range(30):
			d = {}
			d['edge_class'] = classes[i]
			d['tip_vertex_index'] = tips[i]
			d['tail_vertex_index'] = tails[i]
			self.edges.append(d)

	def set_up_faces(self):
		f = [None] * 12
		f[0] = {}
		f[0]['edge_indices'] = [4, 3, 2, 1, 0]
		f[0]['edge_image_indices'] = [9, 8, 7, 6, 5]
		f[0]['edge_orientations'] = [-1] * 5
		f[0]['vertex_indices'] = [4, 3, 2, 1, 0]
		f[0]['vertex_image_indices'] = [15, 19, 18, 17, 16]

		f[1] = {}
		f[1]['edge_indices'] = [5, 6, 7, 8, 9]
		f[1]['edge_image_indices'] = [0, 1, 2, 3, 4]
		f[1]['edge_orientations'] = [1] * 5
		f[1]['vertex_indices'] = [15, 16, 17, 18, 19]
		f[1]['vertex_image_indices'] = [4, 0, 1, 2, 3]

		# ~ even_base_lowest = [0,15,25,20,15]
		# ~ odd_base_lowest = [10,5,10,25,20]
		# ~ even_image_lowest = [10,20,25,10,5]
		# ~ odd_image_lowest = [0,15,20,25,15]

		even_base_start = [0, 2, 0, 4, 1]
		odd_base_start = [0, 1, 4, 2, 2]
		even_image_start = [0, 2, 2, 4, 1]
		odd_image_start = [0, 1, 4, 0, 2]

		v_even_base_start = [0, 1, 1, 0, 0]
		v_odd_base_start = [3, 3, 2, 2, 3]
		v_even_image_start = [3, 3, 3, 2, 2]
		v_odd_image_start = [1, 0, 0, 0, 1]

		for i in range(2, 12, 2):
			f[i] = {}
			f[i]['edge_indices'] = list_sum([0, 15, 25, 20, 15], even_base_start)
			f[i]['edge_image_indices'] = list_sum([10, 20, 25, 10, 5], even_image_start)
			f[i]['edge_orientations'] = [1, -1, -1, -1, 1]
			f[i]['vertex_indices'] = list_sum([0, 0, 5, 10, 5], v_even_base_start)
			f[i]['vertex_image_indices'] = list_sum([15, 10, 5, 10, 15], v_even_image_start)

			f[i + 1] = {}
			f[i + 1]['edge_indices'] = list_sum([10, 5, 10, 25, 20], odd_base_start)
			f[i + 1]['edge_image_indices'] = list_sum([0, 15, 20, 25, 15], odd_image_start)
			f[i + 1]['edge_orientations'] = [-1, -1, 1, 1, 1]
			f[i + 1]['vertex_indices'] = list_sum([10, 15, 15, 10, 5], v_odd_base_start)
			f[i + 1]['vertex_image_indices'] = list_sum([0, 0, 5, 10, 5], v_odd_image_start)

			even_base_start = increase_by_1_mod_5(even_base_start)
			odd_base_start = increase_by_1_mod_5(odd_base_start)
			even_image_start = increase_by_1_mod_5(even_image_start)
			odd_image_start = increase_by_1_mod_5(odd_image_start)

			v_even_base_start = increase_by_1_mod_5(v_even_base_start)
			v_odd_base_start = increase_by_1_mod_5(v_odd_base_start)
			v_even_image_start = increase_by_1_mod_5(v_even_image_start)
			v_odd_image_start = increase_by_1_mod_5(v_odd_image_start)

		self.faces = f

	# noinspection PyUnusedLocal
	def vertex_list(self, param=True):
		return self.vertices

	def face_list(self):
		return self.faces

	def edge_list(self):
		return self.edges


def increase_by_1_mod_5(list_obj):
	return [(i + 1) % 5 for i in list_obj]


def list_sum(l1, l2):
	assert len(l1) == len(l2)
	list_obj = []
	for i in range(len(l1)):
		list_obj.append(l1[i] + l2[i])
	return list_obj


# returns a list of 5 numbers such that all the numbers increase by 1 mod 5 and are in the
# same chunk of 5 (e.g. if n = 17, the list is [17,18,19,15,16]
def mod_5_range(n):
	r = n % 5
	q = int((n - r) / 5)
	return [5 * q + (r + i) % 5 for i in range(5)]


class TwoStructure:
	def __init__(self):
		self.faces = []
		self.vertices = []
		self.edges = []

	# noinspection PyDictCreation
	@staticmethod
	def face_list():
		face1 = {}
		face1['vertex_indices'] = [0, 1, 3, 2]
		face1['vertex_image_indices'] = [0, 1, 3, 2]
		face1['edge_indices'] = [0, 3, 2, 1]
		face1['edge_image_indices'] = [0, 3, 2, 1]
		face1['edge_orientations'] = [1, 1, -1, -1]
		face2 = {}
		face2['vertex_indices'] = [0, 2, 3, 1]
		face2['vertex_image_indices'] = [0, 2, 3, 1]
		face2['edge_indices'] = [1, 2, 3, 0]
		face2['edge_image_indices'] = [1, 2, 3, 0]
		face2['edge_orientations'] = [1, 1, -1, -1]
		return [face1, face2]

	# noinspection PyUnusedLocal
	@staticmethod
	def vertex_list(param=True):
		vertices = []
		for i in range(4):
			vertices.append({'class_index': 0})
		return vertices


# noinspection PyArgumentList
snappySWDomain = snappy.DirichletDomainHP(generator_file='./dodecahedralgenerators.gens',
											maximize_injectivity_radius=False)


def display_snappy_sw_info():
	DD = TwistableDomain(snappySWDomain)

	first_shell = DD.face_list[7].vertices
	first_shell = first_shell[3:] + first_shell[0:3]
	last_shell = DD.face_list[6].vertices

	good_middleshell_indices = [14, 19, 18, 17, 1, 8, 9, 7, 15]
	good_middleshell = [DD.vertices[i] for i in good_middleshell_indices]
	middle_shell = [vertex for vertex in DD.vertices if vertex not in first_shell
					and vertex not in last_shell and vertex not in good_middleshell]
	# first_shell = [DD.vertices[i] for i in [0, 2, 4, 5, 6]]
	# last_shell = []
	# print([face.index for face in DD.face_list if DD.vertices[0] in face.vertices
	# 			and DD.vertices[2] in face.vertices and DD.vertices[4] in face.vertices])
	G = nx.DiGraph(DD.digraph)
	pos = nx.shell_layout(G, nlist=[first_shell, good_middleshell + middle_shell, last_shell])
	nx.draw_networkx_nodes(G, pos)
	edges = nx.get_edge_attributes(G, 'data')
	colors = ['red', 'green', 'blue', 'orange', 'purple', 'yellow']
	preferred_edges = [edge for edge in edges.keys() if edges[edge].orbit.preferred is edges[edge]]
	for i in range(len(DD.edge_orbits)):
		nx.draw_networkx_edges(G, pos, [edge for edge in edges.keys() if edges[edge].orbit.index == i],
							edge_color=colors[i], width=3)
	nx.draw_networkx_edges(G, pos, preferred_edges, edge_color='black', alpha=.2, width=8)

	nx.draw_networkx_labels(G, pos=pos, labels={vertex: 'v{0}'.format(vertex.index) for vertex in G.nodes})

	print(edges)
	# nice_edges = {key:edge.in}
	print({edge: 'e{0}'.format(edges[edge].index) for edge in edges.keys()})
	nx.draw_networkx_edge_labels(DD.digraph, pos,
								edge_labels={edge: 'e{0}'.format(edges[edge].orbit.index) for edge in edges.keys()})

	for face in DD.face_list:
		print('f%s' % face.index)
		print(['v%s' % vertex.index for vertex in face.vertices])
	plt.savefig('./pictures/sw_snappy_digraph.svg')


def random_closed_manifold(num_crossings, num_components=2):
	while True:
		L = spherogram.random_link(num_crossings, num_components)
		exterior = L.exterior()
		exterior = exterior.high_precision()
		exterior.dehn_fill([(0, 1)]*exterior.num_cusps())
		if exterior.volume() < .2:
			continue
		try:
			exterior.dirichlet_domain()
		except RuntimeError as e:
			if str(e) == 'The Dirichlet construction failed.':
				continue
			else:
				raise e
		if exterior.homology().betti_number() == num_components:
			break
	return exterior


# SW2 = snappy.Manifold('ododecld01_00007(1,0)')


if __name__ == '__main__':
	from twistable_revamp import TwistableDomain
	import networkx as nx
	import matplotlib.pyplot as plt
	display_snappy_sw_info()
