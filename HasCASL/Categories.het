library Categories

logic HasCASL

spec Category =
  sorts Ob, Mor
  ops dom,cod : Mor -> Ob;
      id : Ob -> Mor;
      __o__ : Mor*Mor ->? Mor;
  forall f,g,h : Mor; a,b:Ob
  . def f o g <=> cod g = dom f
  . def f o g => dom f o g = dom g
  . def f o g => cod f o g = cod f
  . f o (g o h) = (f o g) o h
  . f o id(dom f) = f
  . id(cod f) o f = f
end

spec ExtCategory[Category] =
  pred __ :: __ --> __ : Mor * Ob * Ob 
  forall f : Mor; a,b : Ob 
  . f :: a --> b <=> dom f = a /\ cod f = b
end

spec Functor =
  Category and {Category with Ob |-> Ob', Mor |-> Mor'}
then
  type Functor = {(fob,fmor) : (Ob -> Ob') * (Mor -> Mor') .
                       forall a:Ob . fob(id(a))=id(fob(a))
                    /\ forall f:Mor . fmor(f)::fob(dom f) --> fob(cod f)
                    /\ forall f,g:Mor . def f o g =>
                               fmor(f o g) = fmor f o fmor g }
end

spec Shape =
  sorts Diagram, Cocone
  preds __isCoconeFor__ : CoCone * Diagram;
        mediates : Mor * Cocone * Cocone
end

spec Colimit[Category][Shape] =
  ExtCategory[Category]
then
  op colimit : Diagram -> (Coconce * (Cocone ->? Mor))
  forall d:Diagram
  . let (c,m) = colimit d
    in c isCoconeFor d
       /\ forall c':Cocone . c' isCoconeFor d <=> def m c'
       /\ def m c' => mediates(m c',c,c')
       /\ forall mor:Mor . mediates(mor,c,c') => mor=m c'
end

spec CoproductShape =
  Category
then
  type CPDiagram := Ob * Ob;
       CPCocone := {(h,k) : Mor * Mor . cod h = cod k}
  pred __isCoconeFor__ : POCoCone * PODiagram
  . ((h,k) as POCocone) isCoconeFor (a,b)  
       <=> dom h = a /\ dom k = b
end

spec PushoutShape =
  Category
then
  type PODiagram = {(f,g) : Mor * Mor . dom f = dom g};
       POCocone = {(h,k) : Mor * Mor . cod h = cod k}
  pred __isCoconeFor__ : POCoCone * PODiagram
  . ((h,k) as POCocone) isCoconeFor ((f,g) as PODiagram)  
       <=> h o f = k o g
end

spec CoequalizerShape =
  Category
then
  type CEDiagram = {(f,g) : Mor * Mor . dom f = dom g /\ cod f = cod g};
       CECocone := Mor
  pred __isCoconeFor__ : CECoCone * CEDiagram
  . (k as CECocone) isCoconeFor ((f,g) as CEDiagram)
       <=> k o f = k o g
end

view CPShape : Shape -> CoproductShape =
  Diagram |-> CPDiagram, CoCone |-> CPCocone
end

spec Coproduct[Category] = 
  Colimit[Category][view CPShape] with colimit |-> __coproduct__
then %def
  ops __objCoproduct__ : Ob * Ob -> Ob
      __ coproduct __ : Mor * Mor -> Mor;
  forall a,b: Ob; f,g:Mor
  . a objCoproduct b =
    let (c,med) = a coproduct b
        (h,k) = c
    in cod h
  . f coproduct g =
      let (c,med) = (dom f) coproduct (dom g)
          (inl,inr) = c
      in med (inl o f, inr o g)
end

view CEShape : Shape -> CoequalizerShape =
  Diagram |-> CEDiagram, CoCone |-> CECocone
end

spec Coequalizer[Category] =
  Colimit[Category][view CEShape] with colimit |-> __coequalizer__
end

view POShape : Shape -> PushoutShape =
  Diagram |-> PODiagram, CoCone |-> POCocone
end

spec Pushout[Category] =
  Colimit[Category][view OPShape]
then %def
  ops __objPushout__ : Mor * Mor -> Ob
  forall a,b: Ob; f,g:Mor
  . f objPushout g =
    let (c,med) = f pushout g
        (h,k) = c
    in cod h
end

spec PushoutAsCoequalizerOfCoproduct
  [Coproduct[Category]] [Coequalizer[Category]] = 
  { %% construction of pushouts from coquealizers + coproducts
  }
end

view v_PushoutAsCoequalizerOfCoproduct :
  Pushout[Category] -> PushoutAsCoequalizerOfCoproduct[Category]
end
