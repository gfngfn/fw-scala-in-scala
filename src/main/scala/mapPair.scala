
trait MapPair {

  type ValueMap = Map[String, ValueDeclBody]
  type TypeMap  = Map[String, TypeDeclBody]

  val body : (ValueMap, TypeMap)


  def getValue(vlabel : String) : Option[ValueDeclBody] =
    body match { case (valmap, _) => valmap.get(vlabel) }


  def getType(tlabel : String) : Option[TypeDeclBody] =
    body match { case (_, tymap) => tymap.get(tlabel) }


  def mergeByRightHandSidePriority[K, V](map1 : Map[K, V], map2 : Map[K, V]) : Map[K, V] =
    map2.foldLeft(map1){ case (map, (k, v)) =>
      map + ((k, v))
    }


  def concat(mapPair2 : MapPair) : MapPair =
    (body, mapPair2.body) match { case ((valmap1, tymap1), (valmap2, tymap2)) =>
      val valmap = mergeByRightHandSidePriority(valmap1, valmap2);
      val tymap = mergeByRightHandSidePriority(tymap1, tymap2);
      new MapPair { val body = (valmap, tymap) }
    }
}

class EmptyMapPair extends MapPair {
  val body = (Map(), Map())
}

class MapPairOfDeclarations(decls : List[Declaration]) extends MapPair {
  val body = {
    val init : (ValueMap, TypeMap) = (Map(), Map());
    decls.foldLeft(init){ case ((valmap, tymap), decl) =>
      decl match {
        case DeclForValueLabel(vl, vd) => (valmap + ((vl, vd)), tymap)
        case DeclForTypeLabel(tl, td)  => (valmap, tymap + ((tl, td)))
      }
    }
  }
}