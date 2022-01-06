#!/usr/bin/pypy3
#
# Handle all cases. Need to run Cluster_Deletion-prep.py first to generate all cases.
# This version does not handle edges between B and C+D. This is handled in Cluster_Deletion2.py

import os, sys, gzip
from copy import deepcopy
from math import ceil

# Compute the branching number for a vector V
def compute(V):
	if len(V) <= 1:
		X = 1
	else:
		low = 1
		high = 10
		ACCURACY = 100000;
		INV_ACCURACY = 1/ACCURACY
		while high-low > INV_ACCURACY:
			mid = (high+low)/2
			v = -1 + sum([mid**(-v) for v in V])
			if v > 0:
				low = mid
			else:
				high = mid
		X = ceil(high * ACCURACY)*INV_ACCURACY
	return X

class Graph:
	def __init__(self, edges):
		self.n = 1 + max([max(x) for x in edges])
		self.A = [[] for i in range(self.n)]
		for e in edges:
			self.A[e[0]].append(e[1])
			self.A[e[1]].append(e[0])

	# Return whether the graph contains an induced P3.
	def find_P3(self):
		for v1 in range(self.n):
			for v2 in self.A[v1]:
				for v3 in self.A[v2]:
					if v3 != v1 and v3 not in self.A[v1]:
						return True
		return False

# Return all subsets of L of size k
def choose(L, k, n = None):
	if n == None:
		n = len(L)
	if k == 0:
		return [[]]
	R = []
	for i in range(k-1,n):
		for S in choose(L, k-1, i):
			R.append(S+[L[i]])
	return R

# Given a graph whose edge set is E, return the size of a minimum deletion set of the graph
def minimum_deletion_set(E):
	L = []
	for k in range(1, len(E)+1):
		for Del in choose(range(len(E)), k):
			E2 = [E[i] for i in range(len(E)) if i not in Del]
			if not Graph(E2).find_P3():
				return k
	return len(E)


# Return a list of adjecent vertices given the adjaceny vector of a vertex
def adj(V):
	return [i for i in range(len(V)) if V[i] == 1]

# Build a graph from a level representation
#
# A level represntation is a tuple (BAmat, BBmat, BB1mat, B1B1mat, B1B2deg)  where
# BAmat[b][a] = 1 if there is an edge between b ∈ B and a ∈ A
# BCdeg[b] = |N(b) ∩ C| for b ∈ B
# BBmat[b][b2] = 1 if there is an edge between b,b2 ∈ B
# BB1mat[b][c] = 1 if there is an edge between b ∈ B and c ∈ B1
# B1B1mat[c][c2] = 1 if there is an edge between c,c2 ∈ B1
# B1B2deg[c] = |N(c) ∩ B2| for c ∈ B1
#
# The returned representation is a vector G in which G[x] is data of vertex x
# G[x][0] = the level of x (the index i such that x ∈ B_i)
# G[x][1] = the neighbors of x.
#
# The vertices are numbered as follows: The 3 vertices of A,
# the vertex of C (if it exists), the vertices of B, the vertices of B1,
# and the vertices of B2.
def build_graph(G0):
	BAmat, BCdeg, BBmat, BB1mat, B1B1mat, B1B2deg = G0
	nB = len(BAmat)
	nB1 = len(B1B2deg)
	nB2 = sum(B1B2deg)
	n = 4+nB+nB1+nB2 # |A|=3
	G = [[None,[]] for i in range(n)]
	G[0][1] = [1]
	G[1][1] = [0,2]
	G[2][1] = [1]
	if max(BCdeg) != 0:
		G[3][1] = [0,1,2]
		for v in range(3):
			G[v][1].append(3)

	# Add edges between A and B
	for b in range(nB):
		for a in adj(BAmat[b]):
			bp = 4+b	# The b-th vertex in B is the bp-th vertex in the ordering of all vertices
			G[bp][1].append(a)
			G[a][1].append(bp)

	# Add edges between vertices of B
	for b in range(nB):
		for b2 in adj(BBmat[b]):
			if b < b2:
				bp = 4+b
				b2p = 4+b2
				G[bp][1].append(b2p)
				G[b2p][1].append(bp)

	# Add edges between B and B1
	for b in range(nB):
		for c in adj(BB1mat[b]):
			bp = 4+b
			cp = 4+nB+c
			G[bp][1].append(cp)
			G[cp][1].append(bp)

	# Add edges between vertices of B1
	for c in range(nB1):
		for c2 in adj(B1B1mat[c]):
			if c < c2:
				cp = 4+nB+c
				c2p = 4+nB+c2
				G[cp][1].append(c2p)
				G[c2p][1].append(cp)

	# Add vertices in B1 according to B1B2deg
	dp = 4+nB+nB1	# an index to the current vertex inserted to B2
	for c in range(nB1):
		for k in range(B1B2deg[c]):
			cp = 4+nB+c
			G[cp][1].append(dp)
			G[dp][1].append(cp)
			dp += 1

	# Initialize the level of the vertices of A and C
	for i in range(4):
		G[i][0] = -1

	# Compute the levels of the vertices of G
	calc_level(G)
	return G

# Compute the levels of the vertices of G (if the level is >! then None value is used instead of the level)
def calc_level(G):
	for i in range(4, len(G)):
		G[i][0] = None
	B = []
	# Find all the vertices in B
	for a in range(3):
		for b in G[a][1]:
			if G[b][0] == None:
				G[b][0] = 0
				B.append(b)

	# Find all the vertices in B1
	for b in B:
		for c in G[b][1]:
			if G[c][0] == None:
				G[c][0] = 1

# Return the indices of the vertices in level 0 (the set B)
def get_B(G):
	return [i for i in range(len(G)) if G[i][0] == 0]

# Return the indices of the vertices in level 1 (the set B1)
def get_B1(G):
	return [i for i in range(len(G)) if G[i][0] == 1]

# Compute the set F_e for an edge e=(b,c) between a vertex b ∈ B and a vertex c ∈ B1
def calcF(G, b, c):
	F = []
	# Add to F edges incident on b
	for x in G[b][1]:
		if G[x][0] == -1:
			F.append((b,x))
		elif x != c and x not in G[c][1]:
			F.append((b,x))
	# Add to F edges incident on c
	for x in G[c][1]:
		if G[x][0] == None:
			F.append((c,x))
		elif x != b and x not in G[b][1]:
			F.append((c,x))
	return F

# Return an edge e=(b,c) between a vertex b ∈ B and a vertex c ∈ B1 with |F_e| >= 3
# If no such edge exists, return None,None
def get_F3_edge(G):
	for b in get_B(G):
		for c in G[b][1]:
			if G[c][0] == 1:
				x = len(calcF(G, b, c))
				if x >= 3:
					return b,c
	return None,None

# delete the edge (b,c) from a graph G
def delete_edge(G,b,c):
	del G[b][1][G[b][1].index(c)]
	del G[c][1][G[c][1].index(b)]

# Compute the size of the set E1 (E1 = edges between B1 and B2)
def calc_E1_size(G):
	r = 0
	for c in get_B1(G):
		for x in G[c][1]:
			if G[x][0] == None: # the level of x must be 2 since x is adjacent to c
				r += 1
	return r

# Compute the signature of the path P = x,y,z in G.
# The signature is a string S where
# If there is a vertex adjacent to x,y,z then S="C".
# Otherwise, S is a string of length 6.
# S[0]/S[1]/S[2]/S[3]/S[4]/S[5] is the number of vertices v in V(G)\{x,y,z} such that
# N(v)∩{x,y,z} is equal {x}/{y}/{z}/{x,y}/{y,z}/{x,z}
def get_signature(G, P):
	S = [0]*6
	for v in range(len(G)):
		if v not in P:
			adj = [int(x in G[v][1]) for x in P] # adj[i] = 1 iff v is adjacent to P[i]
			if adj == [1,1,1]:
				return "C"
			if adj == [1,0,0]:
				S[0] += 1
			elif adj == [0,1,0]:
				S[1] += 1
			elif adj == [0,0,1]:
				S[2] += 1
			elif adj == [1,1,0]:
				S[3] += 1
			elif adj == [0,1,1]:
				S[4] += 1
			elif adj == [1,0,1]:
				S[5] += 1
	return "".join([str(x) for x in S])

# Compute X(G, [0,1,2]) (X(G, A) is an upper bound on bn(G, A))
def compute_X(G, depth = 0):
	if verbose or depth == 0:
		for i in range(len(G)):
			print(i,G[i])
		print("depth =", depth)

	b,c = get_F3_edge(G)
	if b == None: # handle the case j > 0
		p = calc_E1_size(G)

		# Construct the set E0 of edges of G[A∪B]
		E0 = []
		for u in range(len(G)):
			if G[u][0] != None and G[u][0] <= 0:
				for v in G[u][1]:
					if u < v and G[v][0] != None and G[v][0] <= 0:
						E0.append((u,v))
		alpha = minimum_deletion_set(E0) # alpha = OPT(G[A∪B])
		if verbose: print("p = %d alpha = %d depth = %d" % (p,alpha,depth))
		V = [alpha+x for x in R[p]]
		return V

	# V is a vector holding the result
	V = []

	if verbose: print("edge",b,c)

	# Generate the graph G2 = G-{bc}
	G2 = deepcopy(G)
	delete_edge(G2,b,c)
	calc_level(G2)
	V += [1+x for x in compute_X(G2, depth+1)]

	# Generate the graph G3 = G-F_bc
	G3 = deepcopy(G)
	F = calcF(G, b, c)
	for x,y in F:
		delete_edge(G3,x,y)
	calc_level(G3)
	if verbose: print("F",b,c,len(F))

	V += [len(F)+x for x in compute_X(G3, depth+1)]
	return V

# Return all the induced P3's in G[A∪B]
def get_paths(G):
	Paths = []
	for v1 in range(len(G)):
		if v1 > 2 and G[v1][0] != 0: continue
		for v2 in G[v1][1]:
			if v2 > 2 and G[v2][0] != 0: continue
			for v3 in G[v2][1]:
				if v3 == v1 or v3 in G[v1][1] or (v2 > 2 and G[v3][0] != 0): continue
				Paths.append([v1,v2,v3])
	return Paths

# Compute Y(G, [0,1,2])
def compute_Y(G):
	V = compute_X(G)
	X = compute(V) # X = X(G,[0,1,2])
	print(f"Sig={get_signature(G, [0,1,2])} {X:.5f} {V}")
	if XC != {}:
		for P in get_paths(G):
			signature = get_signature(G, P)
			if signature in XC:
				X2 = XC[signature] # X2 = X'(G,P)
				print(P,signature+":"+str(X2))
				X = min(X, X2)
			else:
				print(P,signature)
		print("BN =", X)

	return X

def prod(A, B):
	C = []
	for a in A:
		C += [a+b for b in B]
	return C

# Compute the vector R
R = [None]*10
R[0] = [0]
R[1] = [1,3]
for i in range(2, 10):
	R[i] = prod(R[i-1],R[1])

verbose = False
filename = "cd.txt"
sfilename = "cd_signatures.txt"
for x in sys.argv[1:]:
	if x == "-v":
		verbose = True
	else:
		filename = x

# XC[S] = max(X(G,A)) taken over all G,A such that the signature of the path A in G is S
XC = {}
if os.path.exists(sfilename):
	for line in open(sfilename).readlines():
		L = line.split()
		if len(L) == 2 and L[0] != "C":
			XC[L[0]] = float(L[1])

if filename.endswith("gz"):
	lines = gzip.open(filename).readlines()
else:
	lines = open(filename).readlines()

I_list = [[eval(lines[i+j]) for j in range(6)] for i in range(0, len(lines), 7)]

XC2 = {}
for i in range(len(I_list)):
	print("------------------------------------------------------")
	G = build_graph(I_list[i])
	signature = get_signature(G, [0,1,2])
	X = compute_Y(G)
	if signature not in XC2:
		XC2[signature] = 1
	XC2[signature] = max(XC2[signature], X)

for signature in XC2.keys():
	print(f"{signature} {XC2[signature]:.5f}")
print(f"{max(XC2.values()):.5f}")

if XC == {} and sfilename != None:
	fh2 = open(sfilename, "w")
	for signature in XC2.keys():
		fh2.write(f"{signature} {XC2[signature]:.5f}\n")
	print(f"File {sfilename} created. Rerun the script to get the upper bound on the branching number.")
