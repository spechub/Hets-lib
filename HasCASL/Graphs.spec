library Graphs

%{ Directed graphs over some arbitrary but fixed node and edge types,
   given by node set and source and target maps.
   Note that the node set may be larger than the range of these maps
   in case that there are isolated nodes. }%

logic HasCASL

spec Bool = 
  sort Bool
  ops False, True : Bool;
end

spec Nat = 
  sort Nat
  ops __+__,__*__,__div__ : Nat*Nat->Nat;
      0,1,2 : Nat
  pred __<__ : Nat*Nat;
end

spec List =
  free type List[Elem] ::= nil | cons(Elem; List[Elem])
end

logic HasCASL

%{ Typed sets are represented by predicates over the type.
   Set membership is just holding of the predicate: x isIn s <=> s x
   Note that for disjoint unions and products, the type changes.  }%

spec Set = Bool then
  var S,T : Type
  type Set S := S ->? Unit;
  ops emptySet : Set S;
      {__} : S -> Set S;
      __isIn__ : S * Set S ->? Unit;
      __subset__ :Pred( Set(S) * Set(S) );
      __union__, __intersection__, __\\__  : Set S * Set S -> Set S;
      __disjoint__ : Pred( Set(S) * Set(S) );
      __*__ : Set S -> Set T -> Set (S*T);
      __disjointUnion__ :  Set S -> Set S -> Set (S*Bool);
      injl,injr : S -> S*Bool;
  forall x,x':S; y:T; s,s':Set S; t:Set(T) 
  . not (x isIn emptySet)
  . x isIn {x'} <=> x=x'
  . x isIn s <=> s x
  . s subset s' <=> forall x:S . (x isIn s) => (x isIn s')
  . (x isIn (s union s')) <=> ((x isIn s) \/ (x isIn s'))
  . (x isIn (s intersection s')) <=> ((x isIn s) /\ (x isIn s'))
  . x isIn s \\ s' <=> x isIn s /\ not (x isIn s')
  . (s disjoint s') <=> ((s intersection s') = emptySet)
  %% . ((x,y) isIn (s * t)) <=> ((x isIn s) /\ (y isIn t))
  . (injl x) = (x,false)
  . (injr x) = (x,true)
  %%. (s disjointUnion s') = ((s * {false}) union (s' * {true}))
end


spec DirectedGraph =
  Set
then
  var N,E : Type
  type Graph N E = { (n,source,target) : Set N * (E->?N) * (E->?N)  .
                      dom source=dom target 
                      /\ (source : dom source --> n)
                      /\ (target : dom target --> n) }
end

%{ Some useful operations on directed graphs. }%

spec RichDirectedGraph =
  DirectedGraph
then %def
  var N,E : Type
  ops emptyGraph : Graph N E;
      nodes : Graph N E -> Set N;
      edges : Graph N E -> Set E;
      sourceMap, targetMap : Graph N E -> (E->?N);
      addNode,removeNode : N -> Graph N E -> Graph N E;
      addEdge : E * N * N -> Graph N E -> Graph N E;
      removeEdge : E -> Graph N E -> Graph N E;
      symmetric, transitive, loopFree, complete : Graph N E;
      __subgraph__, __cliqueOf__, __maxCliqueOf__ : Pred(Graph N E * Graph N E);
      __union__, __intersection__ : Graph N E * Graph N E -> Graph N E

  forall n,n1,n2:N; e,e1,e2:E; g,g':Graph N E;
         nn : Set N
  . emtpyGraph = (emptySet,emptyMap,emptyMap) as Graph N E %(emtpyGraph)%

  . nodes (nn,s,t) = nn

  . edges (nn,source,target) = dom source                    %(edges)%

  . sourceMap (nn,source,target) = source

  . targetMap (nn,source,target) = target

  . addNode n (nn,source,target) =
    (nn union {n}, source, target) as Graph N E            %(addNode)%

  . removeNode n (nn,source,target) =
    (nn \\ {n}, source, target) as Graph N E             %(removeNode)%

  . addEdge (e,n1,n2) (nn,source,target) =
    (nn union {n1} union {n2},
     source[e/n1], target[e/n2])                              %(addEdge)%

  . removeEdge e (nn,source,target) =
    (nn, source-e, target-e)                            %(removeEdge)%

  . symmetric g <=> 
    forall e:E .
        e isIn edges g => 
        exists e':E . e' isIn edges g 
                      /\ sourceMapMap g e = targetMap g e'
                      /\ targetMap g e' = targetMap g e      %(symmetric_def)%

  . transitive g <=>
    forall e1,e2:E .
      e1 isIn egdes g /\ e2 isIn edges g /\
      targetMap g e1 = sourceMap g e2 =>
      exists e3:E . e3 isIn edges g
                    /\ sourceMap e3 g = sourceMap e1 g
                    /\ targetMap e3 g = targetMap e2 g      %(transitive_def)%

  . loopFree g <=>
    not (exists e:E . e isIn edges g /\ sourceMap e g = targetMap e g)
                                                              %(loopFree_def)%

  . g1 subgraph g2 <=>
    (forall n:N . n isIn nodes g1 => n isIn nodes g2) /\
    (forall e:E . e isIn edges g1 => e isIn edges g2) /\
    sourceMap g1 = sourceMap g1 intersection sourceMap g2
    targetMap g1 = targetMap g1 intersection targetMap g2
                                                              %(subgraph_def)%

  . complete (nn,source,target) <=>
    forall n1,n2:N . n1 isIn nn /\ n2 isIn nn =>
      exists e:E . source e = n /\ target e = n                   %(complete)%

  . g1 cliqueOf g2 <=>
    g1 subgraph g2 /\ complete(g1)                            %(cliqueOf_def)%

  . g1 maxCliqueOf g2 <=>
    g1 cliqueOf g2
    /\ forall g3:Graph N E . 
        g1 subgraph g3 /\ g3 cliqueOf g2 => g1=g3         %(max_cliqueOf_def)%

  . g union g' = 
    (nodes g union nodes g',
     sourceMap g union sourceMap g',
     targetMap g union targetMap g') as Graph N E

  . g intersection g' = 
    (nodes g intersection nodes g',
     sourceMap g intersection sourceMap g',
     targetMap g intersection targetMap g') as Graph N E
end


spec SimpleGraph =
  RichDirectedGraph
then
  type SimpleGraph N E = {(nn,source,target):Graph N E .
                          forall e1,e2:E . source e1 = source e2
                                          /\ target e1 = target e2 => e1=e2 }
  type LoopFreeGraph N E = {g:Graph N E . loopFree g}
end


spec GraphHomomorphism =
  DirectedGraph
then
  var N1, E1, N2, E2, N3, E3 : Type
  type Hom N1 E1 N2 E2 = 
     {(g1,hn,he,g2) : Graph N1 E1 * (N1->?N2) * (E1->?E2) * Graph N2 E2 .
       hn :: nodes g1 --> nodes g2 /\ he :: edges g1 --> edges g2 
       /\ forall e:E1 . e isIn edges e =>
          (   hn(source g1 e) = source g2 (he e)
           /\ hn(target g1 e) = target g2 (he e) ) } 
  type HomHom E N = Hom E N E N
  ops dom : Hom N1 E1 N2 E2 -> Graph N1 E1;
      cod : Hom N1 E1 N2 E2 -> Graph N2 E2;
      nodeMap : Hom N1 E1 N2 E2 -> (N1->?N2);
      edgeMap : Hom N1 E1 N2 E2 -> (E1->?E2);
      __o__ : Hom N2 E2 N3 E3 * Hom N1 E1 N2 E2 ->? Hom N1 E1 N3 E3
  forall g1:Graph N1 E1; hn:N1->?N2; he:E1->?E2; g2:Graph N2 E2; 
         h1:Hom N1 E1 N2 E2; h2:Hom N2 E2 N3 E3
  . dom ((g1,hn,he,g2) as Hom N1 E1 N2 E2) = g1
  . cod ((g1,hn,he,g2) as Hom N1 E1 N2 E2) = g2
  . nodeMap ((g1,hn,he,g2) as Hom N1 E1 N2 E2) = hn
  . edgeMap ((g1,hn,he,g2) as Hom N1 E1 N2 E2) = he
  . def h2 o h1 <=> cod h1 = dom h2
  . def h2 o h1 => 
    h2 o h1 = 
     (dom h1, nodemap h2 o nodemap h1, edgemap h2 o edgemap h1,cod h2)
      as Hom N1 E1 N2 E2
end

%{ Coproducts of directed graphs, defined in terms of the corresponding
   operations on sets, acting component wise.
   Note that we have to fix N and E here, since we need set representations for them
   in order to get the needed constructions on sets. }%
%[
spec GraphCoproducts [SetRepresentation with S |-> N] [SetRepresentation with S |-> E] =
  AbstractSetConstructions[SetRepresentation with S |-> N]
and
  AbstractSetConstructions[SetRepresentation with S |-> E]
and GraphHomomorphism
then
  ops __coproduct__ : Graph N E * Graph N E -> Graph N E;
                
  forall g,g1,g2: Graph N E
  . g1 coproduct g2 = 
    let (cn,medn) = nodes g1 coproduct nodes g2
        (ce,mede) = edges g1 coproduct egdes g2
        (inln,inrn) = cn   
        (inle,inre) = ce
        g = (cod inl,
             %% needs to be reformulated, since inl, inr are not constructors
             \y:E -> case y of (inle x) -> inln o (sourceMap g1) x
                               (inre x) -> inrn o (sourceMap g2) x,
             \y:E -> case y of (inle x) -> inln o (targetMap g1) x
                               (inre x) -> inrn o (targetMap g2) x)
        inlg = (g1,inln,inle,g) as HomHom N E
        inrg = (g2,inrn,inre,g) as HomHom N E
        medg c1 = let (h,k) = c1
                  in (g,medn (nodeMap h,nodeMap k),mede (edgeMap h,edgemap k),cod h)
    in ((inlg,inrg),medg)
end

%{ Constructions on directed graphs, defined in terms of the corresponding
   operations on sets, usually acting component wise.
   Note that we have to fix N and E here, since we need set representations for them
   in order to get the needed constructions on sets. }%
spec GraphCoequalizers [SetRepresentation with S |-> N] [SetRepresentation with S |-> E] =
  AbstractSetConstructions[SetRepresentation with S |-> N]
and
  AbstractSetConstructions[SetRepresentation with S |-> E]
and GraphHomomorphism
then
  type Congruence = {(g,rn,re) : Graph N E * PER N * PER E
                          . nodes g = dom rn /\ edges g = dom re /\
                            forall e1,e2:E . (e1,e2) isIn re =>
                               (sourceMap g e1,sourceMap g e2) isIn rn /\
                               (targetMap g e1,targetMap g e2) isIn rn }
  ops graph : Congruence -> Graph N E;
      nodeRel : Congruence -> PER N;
      edgeRel : Congruence -> PER E;
      factor : Congruence ->? Graph N E;
      __coproduct__ : Graph N E * Graph N E -> Graph N E;
      pushout : HomHom N E -> HomHom N E ->? 
                HomHom N E * HomHom N E * Med (Graph N E) (HomHom N E)
                

  forall g,g1,g2: Graph N E; h1,h2:HomHom N E; r:Relation N E

  . ((g,rn,re) in Congruence)
    => graph ((g,rn,re) as Congruence) = g
  . ((g,rn,re) in Congruence)
    => nodeRel ((g,rn,re) as Congruence) = rn
  . ((g,rn,re) in Congruence)
    => edgeRel ((g,rn,re) as Congruence) = re

  . factor c =
    (factor (graph c) (nodeRel c),
     mediate (edgeRel c) (coeq (nodeRel c) o sourceMap (graph c)),
     mediate (edgeRel c) (coeq (nodeRel c) o targetMap (graph c)) )

  . g1 coproduct g2 = 
    (nodes g1 coproduct nodes g2,
     sourceMap g1 coproduct sourceMap g2,
     targetMap g1 coproduct targetMap g2)
end
]%
