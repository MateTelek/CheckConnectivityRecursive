###
#A Julia implementation of the algorithm 'CheckConnectivityRecursive' 
#from [Máté L. Telek, Geometry of the signed support of a multivariate polynomial and Descartes' rule of signs, 2024.] 
#using OSCAR and Polymake. 
####

function CheckConnectivityRecursive(supp,A,B, restr_level = 0)
#Implementation of Algorithm 1
#Check some sufficient conditions for connectivity of the preimage of the negative real line
#INPUT
#    supp   ---   pm::Matrix<pm::Rational>   ---   each row has the form [1, exponent vector]
#    A   ---   Vector{Any}   ---   contains indicies of the positive exp. vectors
#    B   ---   Vector{Any}   ---   contains indicies of the negative exp. vectors  
#OUTPUT
#    IsConnected ---   boolean   ---   true, if the preimage of the negative real line connected
#                                ---   false, if the method is inconclusive
    IsConnected = false
  
   #Check strict separating vector
   if check_strictsepvector(supp,A,B)
        IsConnected = true
        println("+++++++++++++++++++++++++++++++++++++++++")
        println("Level: "*string(restr_level))
        print_details(supp,A,B)
        println("The support has a strict separating hyperplane")
        return IsConnected,restr_level
   end
    
    #Check one negative exponent
    if length(B) == 1
        IsConnected = true
        println("+++++++++++++++++++++++++++++++++++++++++")
        println("Level: "*string(restr_level))
        print_details(supp,A,B)
        println("The polynomial has one negative coefficient")
        return IsConnected,restr_level
    end
    
    #Check one posisitve exponent 
    if length(A) == 1 && ngens(parent(f)) > 1
        IsConnected = true
        println("+++++++++++++++++++++++++++++++++++++++++")
        println("Level: "*string(restr_level))
        print_details(supp,A,B)
        println("The polynomial has one positive coefficient")
        return IsConnected,restr_level
    end
    
    #Find the smallest face containing the negative exponent vectors
    F,FA,FB = restr_negface(supp,A,B)
    #Reduce the polynomial to the negative face if the negative face is proper
    if nrows(F) < nrows(supp)
        IsConnected,restr_level1 = CheckConnectivityRecursive(F,FA,FB,restr_level + 1)
        println("+++++++++++++++++++++++++++++++++++++++++")
        println("Level: "*string(restr_level))
        print_details(supp,A,B)
        println("We restrict the polynomial to a proper face that contains all the negative exponent vectors")
        return IsConnected,restr_level
    end
     
    #Compute parallelfaces
    ListOfParallelFaces = parallel_faces(F,FA,FB)
 
    #Check connectivity of the parallel faces
    #If ListOfParallelFaces is empty then the loop does nothing
    count_pairs = 1
    for Gpair in ListOfParallelFaces
        if IntersectionNonempty(Gpair)
            if  CheckConnectivityRecursive(Gpair[1][1],Gpair[1][2],Gpair[1][3],restr_level + 1)[1] &&
                CheckConnectivityRecursive(Gpair[2][1],Gpair[2][2],Gpair[2][3],restr_level + 1)[1]

                println("+++++++++++++++++++++++++++++++++++++++++")
                println("Level: "*string(restr_level))
                print_details(supp,A,B)
                println("There are "*string(length(ListOfParallelFaces))*" pairs of parallel faces that will be checked.")
                println("pair: "*string(count_pairs))

                IsConnected = true
                return IsConnected,restr_level
            end
        end
        count_pairs = count_pairs + 1
    end
    
    return IsConnected,restr_level
end

function signed_support(f)
#Compute the signed support of the polynomial
#INPUT
#    f   ---   fmpq_mpoly
#OUTPUT
#    supp   ---   pm::Matrix<pm::Rational>   ---   each row has the form [1, exponent vector]
#    A   ---   Vector{Any}   ---   contains indicies of the positive exponent vectors
#    B   ---   Vector{Any}   ---   contains indicies of the negative exponent vectors
    
    coeff = collect(Oscar.coefficients(f))
    monos = collect(Oscar.monomials(f)) 
    coeff = collect(Oscar.coefficients(f))
    supp = Vector{Int64}[] 
    for i in 1:length(monos)
        push!(supp,exponent_vector(monos[i],1))
    end
    
    #Get signed support but ONLY the indicies
    A = []
    B = []
    for i in 1:length(supp)
        if coeff[i] > 0
            push!(A,i) 
        else
            push!(B,i) 
        end
    end
        
    P = convex_hull(supp)
    #Convert OSCAR polyhedron to a Polymake Big.Object
    Ppolym = P.pm_polytope
    point = Ppolym.POINTS #WARNING! the points here are in homogeneous coordinates
    facet = Ppolym.FACETS #Here the first entry is the constant term of the facet defining equality
    
    #Check whether the ordering of 'point' and 'supp' are the same
    same_ord = true
    for i in 1:length(supp)
        for j in 1:ngens(parent(f))
            if !(point[i,j+1] == supp[i][j])
                println("The ordering is not the same")
                same_ord = false
            end
        end
    end
    
    #if same_ord
     #   println("The ordering is the same.")
    #end
    return point,A,B
end


function restrict_to(q,supp)
#Restrict the polynomial q to the exponents given in supp
#INPUT
#    q   ---   fmpq_mpoly
#    supp   ---   pm::Matrix<pm::Rational>   ---   each row has the form [1, exponent vector]
#OUTPUT
#    q_rest   ---   fmpq_mpoly
    
    supp_q = signed_support(q)[1]
    coeff = collect(coeffs(q))
    mono = collect(monomials(q))
    q_rest = R(0)
    
    for i in 1:nrows(supp)
        for j in 1:nrows(supp_q)
            if supp[i,:]==supp_q[j,:]
                q_rest = q_rest + coeff[j]*mono[j]
                break
            end
        end
    end
    
    return q_rest
end

function restr_negface(supp,A,B)
#Restrict the polynomial to the negative face
#INPUT
#    supp   ---   pm::Matrix<pm::Rational>   ---   each row has the form [1, exponent vector]
#    A   ---   Vector{Any}   ---   contains indicies of the positive exp. vectors
#    B   ---   Vector{Any}   ---   contains indicies of the negative exp. vectors
#OUTPUT
#    suppF   ---   pm::Matrix<pm::Rational>   ---   each row has the form [1, exponent vector]
#    QA   ---   Vector{Any}   ---   contains indicies of the positive exp. vectors
#    QB   ---   Vector{Any}   ---   contains indicies of the negative exp. vectors
   
    P = Polymake.polytope.Polytope(POINTS=supp)
    INC = P.POINTS_IN_FACETS
    
    VeryNegFacet = [] #facets containing all the negative exponent vectors
    for i in 1:P.N_FACETS
        cont_all_neg = true
        for b in B
            if !getindex(INC,i,b)
                cont_all_neg = false
                break
            end
        end
        if cont_all_neg
            push!(VeryNegFacet,i)
        end
    end
    
   #Collect all the positive monomials on the VeryNegFacet
    FA = []
    for a in A
        IsOnF = true
        #If VeryNegFacet is empty then for loop does not do anything and FA = A is returned
        for i in VeryNegFacet
            if !getindex(INC,i,a)
                IsOnF = false
                break
            end
        end
        if IsOnF
            push!(FA,a)
        end
    end
    
    #Initialize a matrix for the exponent vectors  
    suppF = Polymake.Matrix{Polymake.Rational}(length(FA)+length(B),ncols(supp))

    #The positive monomials are at the top of the matrix suppF
    QA = [i for i in 1:length(FA)]
    for i in 1:length(FA)
        suppF[i,:] = supp[FA[i],:]
    end
    
    ##The negative exponent vectors are at the bottom of the matrix suppF
    QB = [i for i in (length(QA)+1):(length(FA)+length(B))]
    for i in 1:length(B)
        suppF[length(QA) + i,:] = supp[B[i],:]
    end

    return suppF,QA,QB
end

function check_strictsepvector(supp,A,B)     
#CHECK SEPARATING HYPERPLANES
#INPUT
#    supp   ---   pm::Matrix<pm::Rational>   ---   each row has the form [1, exponent vector]
#    A   ---   Vector{Any}   ---   contains indicies of the positive exp. vectors
#    B   ---   Vector{Any}   ---   contains indicies of the negative exp. vectors
#OUTPUT
#   SepVecFound --- boolean

    #Build the inequalities, they have the form  
    #     0 <= (c v)*(1 -a) for all positive exponents a 
    #     0 <= (c v)*(-1 b) for all negative exponents b
    M = copy(supp)
    for a in A
        M[a,:] = -copy(supp)[a,:]
        M[a,1] = -M[a,1]
    end

    for b in B
        M[b,1] = -M[b,1]
    end
    
    SepCone = Polymake.polytope.Cone(INEQUALITIES=M)
    vc = SepCone.REL_INT_POINT
    
    #If there is no separating vector return false
    if typeof(SepCone.REL_INT_POINT) == Nothing
        return false
    end
    
    #Check whether the separating vector is strict
    SepVec_found = false 
        
    for b in B      
        if dot(M[b,:],vc) != 0
             SepVec_found = true
             break
        end
    end
    
   #if printing
   #    if SepVec_found
   #        println("A strict separating vector is found. The preimage of the negative real line is path connected.")
   #    else
   #        println("The support set does not have a strict separating vector.")
   #    end
   #end
            
    return SepVec_found
end

function IntersectionNonempty(Gpair)
#Input
#   a vector of the form [Gsupp,GA,GB],[Gopp_supp,GoppA,GoppB] where
#   suppG,suppGopp   ---   pm::Matrix<pm::Rational>    ---   each row has the form [1, exponent vector]
#   GA,GoppA   ---   Vector{Any}   ---   contains indicies of the positive exp. vectors
#   GB,GoppB   ---   Vector{Any}   ---   contains indicies of the negative exp. vectors
#OUTPUT
#   CommonNegVertex --- boolean   ---   true if a common negative vertex exists
        
    G = Gpair[1][1]
    GB = Gpair[1][3]
    Gopp = Gpair[2][1]
    GBopp = Gpair[2][3]
    
    F = Polymake.polytope.Polytope(POINTS=vcat(G,Gopp))

    #Find the vertices of F that correspond to negative exponent vectors in G resp. in Gopp
    FG_negvertex = []
    FGopp_negvertex = []
    for i in 1:F.N_VERTICES
        #Collect all the indicies of vertices of F that correspond negative exponent vectors in G
        for j in GB
            if F.VERTICES[i,:] == G[j,:]
                FG_negvertex = push!(FG_negvertex,i)
            end
        end
        
        #Collect all the indicies of vertices of F that correspond negative exponent vectors in Gopp
        for j in GBopp
            if F.VERTICES[i,:] == Gopp[j,:]
                FGopp_negvertex = push!(FGopp_negvertex,i)
            end
        end
    end
    
    #Vertex-facet incidence matrix, with rows corresponding to facets and columns to vertices
    M = F.VERTICES_IN_FACETS
    d = Polymake.polytope.dim(F)
    #Consider all pairs of negative vertices of F
    for i in FG_negvertex
        for j in FGopp_negvertex
            #Check if the pair (i,j) gives a negative edge
            
            #Number of facets containing i and j
            num_cont_facets = 0
            
            #Find all the facets containing i and j
            for k in 1:F.N_FACETS
                if M[k,i] && M[k,j]
                    num_cont_facets = num_cont_facets + 1
                end
            end
            
             #If number of facets containing i and j is larger or equal than dim(F)-1 than i,j gives an edge of F
            if num_cont_facets >= d-1
                return true
            end
            
        end
    end
    
    return false
end

function parallel_faces(supp,A,B)
#Compute all the parallel faces
#INPUT
#    supp   ---   pm::Matrix<pm::Rational>   ---   each row has the form [1, exponent vector]
#    A   ---   Vector{Any}   ---   contains indicies of the positive exp. vectors
#    B   ---   Vector{Any}   ---   contains indicies of the negative exp. vectors
#OUTPUT
#   list containing pairs [Gsupp,GA,GB],[Gopp_supp,GoppA,GoppB] where
#   suppG,suppGopp   ---   pm::Matrix<pm::Rational>    ---   each row has the form [1, exponent vector]
#   GA,GoppA   ---   Vector{Any}   ---   contains indicies of the positive exp. vectors
#   GB,GoppB   ---   Vector{Any}   ---   contains indicies of the negative exp. vectors

    Qpolym = Polymake.polytope.Polytope(POINTS=supp)
    facetQ = Qpolym.FACETS
    pointQ = Qpolym.POINTS
    
    #Compute parallel facet
    parallel_face = []
    parallel_face_const = []
    
    for k in 1:Qpolym.N_FACETS
        dot_prods = []
        for i in 1:Qpolym.N_POINTS
            #Compute the dot product of two vectors
            push!(dot_prods,dot(facetQ[k,:],pointQ[i,:]))
        end
        

        if length(Set{Int}(dot_prods)) == 2
            push!(parallel_face,k)
            push!(parallel_face_const,minimum(dot_prods)) #to make sure that G is a facet and not Gopp, we take the minimum
        end
    end
    
  
    ListOfParallelFaces = []
    #Run through all the parallel faces
    for k in 1:length(parallel_face)
        i = parallel_face[k]
        #Find the indices for points in G and Gopp
        G = []
        Gopp = []

       for j in 1:Qpolym.N_POINTS
          if dot(facetQ[i,:],pointQ[j,:]) == parallel_face_const[k]
              push!(G,j)
          else
              push!(Gopp,j)
          end
       end
               
       #Compute the support of G and Gopp
       suppG = Qpolym.POINTS[G,:] 
       suppGopp =  Qpolym.POINTS[Gopp,:]
        
       #Compute GA and GB from A and B     
       GA = []
       GB = []
       for j in 1:length(G)
          if G[j] in A
               push!(GA,j)
           else
               push!(GB,j)
           end
       end
       
       #Compute GoppA and GoppB from A and B    
       GoppA = []
       GoppB = []
       for j in 1:length(Gopp)
          if Gopp[j] in A
               push!(GoppA,j)
           else
               push!(GoppB,j)
           end
        end      
        push!( ListOfParallelFaces,[[suppG,GA,GB],[suppGopp,GoppA,GoppB]])
    end
   
    return ListOfParallelFaces
end     

function print_details(supp,A,B)
#Check some conditions for connectivity of the preimage of the negative real line
#INPUT
#    supp   ---   pm::Matrix<pm::Rational>   ---   each row has the form [1, exponent vector]
#    A   ---   Vector{Any}   ---   contains indicies of the positive exp. vectors
#    B   ---   Vector{Any}   ---   contains indicies of the negative exp. vectors  
#OUTPUT
    P = Polymake.polytope.Polytope(POINTS=supp)
    println("dimension of the Newton polytope:  "*string(Polymake.polytope.dim(P)))
    println("# of pos. exponent vectors: "*string(length(A))*" # of neg. exponent vectors: "*string(length(B)))
    
end

function check_connectivity_rn(rn)
#Check some sufficient conditions for connectivity of the parameter region of multistationarity
#    rn  ---   ReactionSystem   --- reaction network generated with Catalyst.jl
#OUTPUT
#    IsConnected ---   boolean   ---   true, if the preimage of the negative real line connected
#                                ---   false, if the method is inconclusive
    q = critical_polynomial(rn)
    supp,A,B = signed_support(q)
    IsConnected = CheckConnectivityRecursive(supp,A,B)[1]
    
    if IsConnected
        println("The parameter region of multistationarity is path connected.")
    else
        println("The method is inconclusive")
    end
    
    return IsConnected
end

function critical_polynomial(rn)
#Compute the critical polynomial of a reaction network 
#INPUT
#    rn  ---   ReactionSystem   --- reaction network generated with Catalyst.jl
#OUTPUT
#    f   ---   fmpq_mpoly
    
    N = netstoichmat(rn)
    
    #Compute the flux cone and its extreme vectors
    matrix_def_cone = vcat(N,-N,-Matrix{Int}(I,ncols(N),ncols(N)))
    C = polyhedron(matrix_def_cone,[0 for i in 1:(nrows(matrix_def_cone))])
    E = Matrix(transpose(matrix(QQ, rays(C))))
    W = rref(matrix(QQ,conservationlaws(N)))[2] #Make sure that W is row reduced
    Y = substoichmat(rn)

    n,r = size(N) #Number of species and reactions
    d = nrows(W) #Number of conservation laws
    lnum = size(E, 2) 
    hnum = size(N, 1) 
    
    #Compute the critical polynomial
    ls = ["L[$i]" for i in 1:lnum]
    hs = ["h[$i]" for i in 1:hnum]
    global R,var = polynomial_ring(QQ, vcat(ls,hs))

    Elambda = E * [gens(R)[i]  for i in 1:lnum]
    D = Matrix(identity_matrix(R,r))
    for i in 1:r
        D[i,i] = Elambda[i]
    end
    
    H = Matrix(identity_matrix(R,hnum))
    for i in 1:hnum
        H[i,i] = gens(R)[lnum+i]  
    end

    J = N*D*transpose(Y)*H
    
    #Find the indicies of the first nonzero coordinate of the rows of W
    #It gives the indicies of the polynomials that we have to replace
    pivot = []
    for i in 1:d
        for j in 1:n
            if W[i,j] != 0
                push!(pivot,j)
                break
            end
        end
    end
    
    for (i, j) in enumerate(pivot)
            # Change row j-th of J by i-th of W
            for k in 1:size(J, 2)
                J[j,k] = R(W[i,k])
            end
    end
    
    s =rank(N)
    return (-1)^s*det(matrix(J))
end