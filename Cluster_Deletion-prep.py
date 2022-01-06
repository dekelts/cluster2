#!/usr/bin/pypy3

# Return a list of adjecent vertices given the adjaceny vector of a vertex
def adj(V):
	return [i for i in range(len(V)) if V[i] == 1]

# Return the set {0,...,n-1}\{ex}
def range_exclude(n, ex):
	return [i for i in range(n) if i != ex]

# Return the set {0,...,n-1}\{ex,ex2}
def range_exclude2(n, ex1, ex2):
	return [i for i in range(n) if i != ex1 and i != ex2]

# Return a list of all monotone sequences of length at most n over the alphabet {0,...,sigma-1}
def all_monotone_sequences(n, sigma):
	if n == 1:
		return [[c] for c in range(sigma)]
	A = all_monotone_sequences(n-1, sigma)
	B = []
	for x in A:
		if len(x) == n-1:
			B += [[c]+x for c in range(x[0]+1)]
	return A+B

# Return a list of all sequences of length n over the alphabet {0,...,sigma-1}
def all_sequences(n, sigma):
	if n == 0:
		return [[]]
	B = []
	for x in all_sequences(n-1, sigma):
		B += [x+[c] for c in range(sigma)]
	return B

# Generate a list of BAmat vectors, where BAmat[b][a] = 1 if there is an edge between b ∈ B and a ∈ A
def generate_BAmat_list():
	R = []
	for X in all_monotone_sequences(4, 6):
		# X is the sequence of the types of the vertices in B (|X| <= 4)
		# The type of a vertex b in B is according to its neighbors in A.
		# Since a vertex in B has 1 or 2 neighbors in A, there are 6 types of vertices.
		# Types 0&1 are vertices in Bu, types 4&5 are vertices in Bv, and types 2&3 are vertices in Bu and Bv
		# We go over monotone sequences to eliminate symetric cases
		if len([c for c in X if c <= 3]) > 2:	# if |Bu| > 2 we skip X
				continue
		if len([c for c in X if c >= 2]) > 2:	# if |Bw| > 2 we skip X
				continue

		BAmat = [[0]*3 for x in X]
		for i,c in enumerate(X):
			if c == 0:
				BAmat[i][0] = 1
			elif c == 1:
				BAmat[i][1] = 1
				BAmat[i][2] = 1
			elif c == 2:
				BAmat[i][1] = 1
			elif c == 3:
				BAmat[i][0] = 1
				BAmat[i][2] = 1
			elif c == 4:
				BAmat[i][2] = 1
			elif c == 5:
				BAmat[i][0] = 1
				BAmat[i][1] = 1
		R.append(BAmat)
	return R

# Generate a list of XXmat vectors, where XXmat[b][b2] = 1 if there is an edge between b,b2 ∈ X
# n is the size of X
def generate_XXmat_list(n):
	R = []
	for X in all_sequences(n*(n-1)/2, 2):
		XXmat = [[0]*n for x in range(n)]
		k = 0
		for i in range(1,n):
			for j in range(i):
				if X[k] == 1:
					XXmat[i][j] = 1
					XXmat[j][i] = 1
				k += 1
		R.append(XXmat)
	return R

# Generate a list of BB1deg vectors, where BB1deg[b] = |N(b) ∩ B1| for b ∈ B
def generate_BB1deg_list(k):
	return [X for X in all_sequences(k, 3) if sum(X) > 0]
	# |N(b) ∩ B1| ∈ {0,1,2} for every b ∈ B so the alphabet size is 3.
	# We need at least one index b with X[b] > 0 otherwise j = infinity

# Generate a list of BCdeg vectors, where # BCdeg[b] = |N(b) ∩ C| for b ∈ B
# We assume that |C| <= 1 (otherwise, it can be shown that B2 is empty,
# so the connected component of u is an almost clique.
# Therefore, BCdeg[b] is 0 or 1.
def generate_BCdeg_list(k):
	return all_sequences(k, 2)

# An item X in the BB1a list is a list of the B1-endpoints of the edges between B and B1 (k = num of edges)
# The edges are ordered according to their B-endpoints.
# For each edge, its B1-endpoint is either the endpoint of a previous edge, or a new vertex.
# Therefore, every element X[i] is in the range 1,2,...,max(X[0],...,X[i-1])
def generate_BB1a_list(k):
	if k == 0:
		return [[]]
	if k == 1:
		return [[1]]
	r = []
	for X in generate_BB1a_list(k-1):
		m = max(X)
		for y in range(1,(m+1)+1):
			r.append(X+[y])
	return r

# Generate a dictionary: BB1mat_dict[BB1deg] is a list of BB1mat vectors that matches BB1deg,
# where BB1mat[b][c] = 1 if there is an edge between b ∈ B and c ∈ B1
def generate_BB1mat_dict():
	BB1a_list = [generate_BB1a_list(k) for k in range(8+1)]
	BB1mat_dict = {}
	for Bsize in range(1,4+1): 	# Bsize is the size of B
		for BB1deg in BB1deg_list[Bsize]: # a list of degrees of the vertices in B
			key = tuple(BB1deg)
			BB1mat_dict[key] = []
			n = sum(BB1deg) # number of B-B1 edges
			for X in BB1a_list[n]:
				m = max(X) # size of B1
				BB1mat = [[0]*m for i in range(4)]
				k = 0
				for b in range(Bsize):
					for i in range(BB1deg[b]): # Add BB1deg[b] edges incident on b
						BB1mat[b][X[k]-1] = 1
						k += 1
				if sum([sum(x) for x in BB1mat]) == n:
				# The condition above is not satisfied if BB1deg+X specifies that there are two
				# edges with same endpoints. In this case, we don't generate BB1mat
					BB1mat_dict[key].append(BB1mat)
	return BB1mat_dict

def generate_B1B2deg_list(k):
	return all_sequences(k, 3)

def test1(BAmat, BCdeg, BBmat, BB1deg):
# BAmat[b][a] = 1 if there is an edge between b ∈ B and a ∈ A
# BCdeg[b] = |N(b) ∩ C| for b ∈ B
# BBmat[b][b2] = 1 if there is an edge between b,b2 ∈ B
# BB1deg[b] = |N(b) ∩ B1| for b ∈ B
	nB = len(BAmat) # nB = |B|

	# check that A-B edges have |Fe| <= 3
	for b in range(nB):	# b is a vertex of B
		for x in adj(BAmat[b]): # x is a neighbor of B in A
			# compute a lower bound f on |F_xb|
			f = 0

			# P3s of the form C-x-b
			f += max(BCdeg)-BCdeg[b]
			# If max(BCdeg)=1 then |C|=1. Let C={y}
			# If y is not adjacent to b, then y-x-b is a P3

			# P3s for the form A-x-b 
			for x2 in range_exclude(3, x): # Go over the vertices of A except x
				xx2edge = 0 if (x,x2) in [(0,2),(2,0)] else 1
				# xx2edge = 1 if xx2 is an edge
				if xx2edge != BAmat[b][x2]:
					f += 1
					# if either xx2 is an edge and bx2 is not an edge, or vice versa, increase f by 1.

			# P3s of the form x-b-B or B-x-b
			for b2 in range_exclude(nB, b): # Go over the vertices of B except b
				if BBmat[b][b2] != BAmat[b2][x]:
					f += 1
					# if either bb2 is an edge and b2x is not an edge, or vice versa, increase f by 1.

			# P3s of the form x-b-B1. For every neighbor c of B in B1, x-b-c is a P3.
			f += BB1deg[b]

			if f > 3:
				return False

	# check that B-B edges have |Fe| <= 3
	for b in range(nB): # b is a vertex in B
		for b2 in adj(BBmat[b]): # b2 is a neighbor of b in B
			f = 0

			# P3s of the form b-b2-A or A-b-b2
			for i in range(3):
				if BAmat[b][i] != BAmat[b2][i]:
					f += 1

			# P3s of the form b-b2-B or B-b-b2
			for b3 in range_exclude2(nB, b, b2):
				if BBmat[b][b3] != BBmat[b2][b3]:
					f += 1

			# P3s of the form b-b2-B1 or B1-b-b2 (lower bound)
			f += abs(BB1deg[b]-BB1deg[b2])
			# Suppose that BB1deg[b2] <= BB1deg[b].
			# Then, b has at least BB1deg[b]-BB1deg[b2] neighbors in B1 that are not adjacent to b2

			# P3s of the form b-b2-C of C-b-b2 (lower bound)
			f += abs(BCdeg[b]-BCdeg[b2])

			if f > 3:
				return False
	return True

def generate_D1_list():
	D1_list = []
	for BAmat in BAmat_list: # The A-B edges
		for BCdeg in BCdeg_list[len(BAmat)]:
			for BBmat in XXmat_list[len(BAmat)]: # The B-B edges
				for BB1deg in BB1deg_list[len(BAmat)]: # The number of B1 neighbors of each vertex in B
					if test1(BAmat, BCdeg, BBmat, BB1deg): # check if this case is legal
						D1_list.append([BAmat, BCdeg, BBmat, BB1deg])
	return D1_list

def test2(BAmat, BCdeg, BBmat, BB1mat):
# BAmat[b][a] = 1 if there is an edge between b ∈ B and a ∈ A
# BCdeg[b] = |N(b) ∩ C| for b ∈ B
# BBmat[b][b2] = 1 if there is an edge between b,b2 ∈ B
# BB1mat[b][c] = 1 if there is an edge between b ∈ B and c ∈ B1
	nB = len(BAmat) # nB = |B|
	nB1 = len(BB1mat[0]) # nB1 = |B1|

	# check B-B edges
	for b in range(nB): # b is a vertex in B
		for b2 in adj(BBmat[b]): # b2 is a neighbor of b in B
			f = 0
			# P3s of the form b-b2-A or A-b-b2
			for i in range(3):
				if BAmat[b][i] != BAmat[b2][i]:
					f += 1

			# P3s of the form b-b2-B or B-b-b2
			for b3 in range_exclude2(nB, b, b2):
				if BBmat[b][b3] != BBmat[b2][b3]:
					f += 1

			# P3s of the form b-b2-B1 or B1-b-b2
			for c in range(nB1): # c is a vertex in B1
				if BB1mat[b][c] != BB1mat[b2][c]:
					f += 1

			# P3s of the form b-b2-C of C-b-b2 (lower bound)
			f += abs(BCdeg[b]-BCdeg[b2])

			if f > 3:
				return False
	return True

def generate_D2_list(D1_list):
	D2_list = []
	for BAmat,BCdeg,BBmat,BB1deg in D1_list:
		for BB1mat in BB1mat_dict[tuple(BB1deg)]:
			if test2(BAmat, BCdeg, BBmat, BB1mat):
				D2_list.append([BAmat, BCdeg, BBmat, BB1mat])
	return D2_list

def test3(BAmat, BCdeg, BBmat, BB1mat, B1B2deg):
# BAmat[b][a] = 1 if there is an edge between b ∈ B and a ∈ A
# BCdeg[b] = |N(b) ∩ C| for b ∈ B
# BBmat[b][b2] = 1 if there is an edge between b,b2 ∈ B
# BB1mat[b][c] = 1 if there is an edge between b ∈ B and c ∈ B1
# B1B2deg[c] = number of neighbors of c in B2, where c ∈ B1
	nB = len(BAmat)

	# check B-B1 edges
	for b in range(nB): # b is a vertex in B
		for c in adj(BB1mat[b]): # c is a neighbor of b in B1
			f = 0

			# P3s of the form A-b-c
			f += sum(BAmat[b])

			# P3s of the form b-c-B
			for b2 in range_exclude(nB, b): # b2 is a vertex in B except b
				if BBmat[b][b2] != BB1mat[b2][c]:
					f += 1

			# Note that we don't know the number of P3s of the form b-c-B1
			# since we don't have information on the B1-B1 edges (this will be done in test4)

			# P3s of the form b-c-B2
			f += B1B2deg[c]

			# P3s of the form C/D-b-c
			f += BCdeg[b]

			if f > 3:
				return False
	return True

def generate_D3_list(D2_list):
	D3_list = []
	for BAmat,BCdeg,BBmat,BB1mat in D2_list:
		n = len(BB1mat[0])
		for B1B2deg in B1B2deg_list[n]:
			if test3(BAmat, BCdeg, BBmat, BB1mat, B1B2deg):
				D3_list.append([BAmat, BCdeg, BBmat, BB1mat, B1B2deg])
	return D3_list

def test4(BAmat, BCdeg, BBmat, BB1mat, B1B1mat, B1B2deg):
# BAmat[b][a] = 1 if there is an edge between b ∈ B and a ∈ A
# BCdeg[b] = |N(b) ∩ C)| for b ∈ B
# BBmat[b][b2] = 1 if there is an edge between b,b2 ∈ B
# BB1mat[b][c] = 1 if there is an edge between b ∈ B and c ∈ B1
# B1B1mat[c][c2] = 1 if there is an edge between c,c2 ∈ B1
# B1B2deg[c] = number of neighbors of c in B2, where c ∈ B1

	nB = len(BAmat)
	nB1 = len(BB1mat[0])

	# check B-B1 edges
	for b in range(nB): # b is a vertex in B
		for c in adj(BB1mat[b]): # c is a neighbor of b in B1

			f = 0

			# P3s of the form A-b-c
			f += sum(BAmat[b])

			# P3s of the form b-c-B
			for b2 in range_exclude(nB, b):
				if BBmat[b][b2] != BB1mat[b2][c]:
					f += 1

			# P3s of the form b-c-B1
			for c2 in range_exclude(nB1, c):
				if BB1mat[b][c2] != B1B1mat[c][c2]:
					f+= 1

			# P3s of the form b-c-B2
			f += B1B2deg[c]

			if f > 3:
				return False

	# check B1-B1 edges
	for c in range(nB1): # c in a vertex in B1
		for c2 in adj(B1B1mat[c]): # c2 is a neighbor of c in B1
			f = 0

			# P3s of the form c-c2-B
			for b in range(nB):
				if BB1mat[b][c] != BB1mat[b][c2]:
					f += 1

			# P3s of the form c-c2-B1
			for c3 in range_exclude2(nB1, c, c2):
				if B1B1mat[c][c3] != B1B1mat[c2][c3]:
					f += 1

			# P3s of the form c-c2-B2 (lower bound)
			f += abs(B1B2deg[c]-B1B2deg[c2])
			if f > 3:
				return False

	return True

def generate_D4_list(D3_list):
	D4_list = []
	for BAmat,BCdeg,BBmat,BB1mat,B1B2deg in D3_list:
		n = len(BB1mat[0]) # size of B1
		for B1B1mat in XXmat_list[n]:
			if test4(BAmat, BCdeg, BBmat, BB1mat, B1B1mat, B1B2deg):
				D4_list.append([BAmat, BCdeg, BBmat, BB1mat, B1B1mat, B1B2deg])
	return D4_list

BAmat_list = generate_BAmat_list()
BCdeg_list = [generate_BCdeg_list(k) for k in range(4+1)]
XXmat_list = [generate_XXmat_list(k) for k in range(6+1)] # |B1| <= 6!
BB1deg_list = [generate_BB1deg_list(k) for k in range(4+1)]
BB1mat_dict = generate_BB1mat_dict()
B1B2deg_list = [generate_B1B2deg_list(k) for k in range(8+1)]

D1_list = generate_D1_list()
print("D1:", len(D1_list))
D2_list = generate_D2_list(D1_list)
print("D2:", len(D2_list))
D3_list = generate_D3_list(D2_list)
print("D3:", len(D3_list))
D4_list = generate_D4_list(D3_list)
print("D4:", len(D4_list))

fh  = open("cd.txt", "w")
for BAmat, BCdeg, BBmat, BB1mat, B1B1mat, B1B2deg in D4_list:
	fh.write(str(BAmat)+"\n")
	fh.write(str(BCdeg)+"\n")
	fh.write(str(BBmat)+"\n")
	fh.write(str(BB1mat)+"\n")
	fh.write(str(B1B1mat)+"\n")
	fh.write(str(B1B2deg)+"\n\n")
fh.close()
