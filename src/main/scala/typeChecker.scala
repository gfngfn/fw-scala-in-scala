
sealed trait TypeError
case class TypeNotAFieldButAMethod(vl : String)            extends TypeError
case class TypeNotAMethodButAField(vl : String)            extends TypeError
case class TypeWrongNumberOfArguments(la : Int, lp : Int)  extends TypeError
case class VariableExtrudesItsScope(x : String, ty : Type) extends TypeError
case class UndefinedVariable(x : String)                   extends TypeError
case class AlreadySeen(did : DeclarationID)                extends TypeError
case class CannotExpandSingletonType(p : Path)             extends TypeError
case class NonEmbodiedTypeLabel(tl : String)               extends TypeError
case class ValueNotFound(vl : String)                      extends TypeError
case class TypeNotFound(tl : String)                       extends TypeError


trait Store {

  val body : Set[DeclarationID]

  def contains(did : DeclarationID) : Boolean =
    body.contains(did)


  def add(did : DeclarationID) : Store =
    new Store { val body = Store.this.body + did }

}

trait EmptyStore extends Store {
  val body = Set.empty
}


trait TypeEnv {

  val body : Map[String, Type]

  def add(x : String, ty : Type) : TypeEnv =
    new TypeEnv { val body = TypeEnv.this.body + ((x, ty)) }


  def findVariable(x : String) : Option[Type] =
    body.get(x)

}

class EmptyTypeEnv extends TypeEnv {
  val body = Map()
}


object FWSTypeChecker {

  var currentMaxID : Int = 0

  def generateFreshVariable() : String = {
    currentMaxID += 1;
    "%v" + currentMaxID
  }


  def typeCheck(store : Store, tyenv : TypeEnv, ast : Ast) : Either[TypeError, Type] =
    ast match {
      case Access(ast0, vlabel) =>
        pathOfAstIfPossible(ast0) match {
          case None =>
          /* -- if the expression 'ast0' is not (interprettable as) a path -- */
            typeCheck(store, tyenv, ast0) flatMap { ty0 =>
              valueMembership(store, tyenv, ty0, vlabel) flatMap {
                case DeclVal(_, ty, _) =>
                  Right(ty)

                case DeclDef(_, _, _, _) =>
                  Left(TypeNotAFieldButAMethod(vlabel))
              }
            }

          case Some(path) =>
            val _ = typeCheckPath(store, tyenv, path);
            Right(SingletonType(path))
        }

      case Call(ast0, vlabel, astargs) =>
        typeCheck(store, tyenv, ast0) flatMap { ty0 =>
          valueMembership(store, tyenv, ty0, vlabel) flatMap {
            case DeclVal(_, _, _) =>
              Left(TypeNotAMethodButAField(vlabel))

            case DeclDef(_, params, tyans, _) =>
              typeCheckParams(store, tyenv, params, astargs) flatMap { _ =>
                Right(tyans)
              }
          }
        }

      case Var(x) =>
        val path : Path = Path(x, Nil);
        typeCheckPath(store, tyenv, path) flatMap { _ =>
          Right(SingletonType(path))
        }

      case ValNewIn(x, ty, ast0) =>
        checkTypeWellFormedness(store, tyenv, ty) flatMap { _ =>
          typeCheck(store, tyenv.add(x, ty), ast0) flatMap { ty0 =>
            if (occursInType(x, ty0)) {
              Left(VariableExtrudesItsScope(x, ty0))
            } else {
              val phi : String = generateFreshVariable();
                /* -- a dummy variable name -- */
              expandType(store, tyenv, phi, ty) flatMap { _ =>
                Right(ty0)
              }
            }
          }
        }

    }


  def typeCheckParams(store : Store, tyenv : TypeEnv, params : List[(String, Type)], astargs : List[Ast]) : Either[TypeError, Unit] = {
    val lenArgs : Int = astargs.length;
    val lenParams : Int = params.length;
    if (lenArgs != lenParams) {
      Left(TypeWrongNumberOfArguments(lenArgs, lenParams))
    } else {
      val pairs : List[((String, Type), Ast)] = params.zip(astargs);
      val resInit : Either[TypeError, Unit] = Right(());
      pairs.foldLeft(resInit){ case (res, ((_, tyParam), astarg)) =>
        res flatMap { _ =>
          typeCheck(store, tyenv, astarg) flatMap { tyArg =>
            isSubtype(store, tyenv, tyArg, tyParam)
          }
        }
      }
    }
  }


  def occursInType(x : String, ty : Type) : Boolean =
    ty match {
      case SingletonType(Path(y, _))    => x == y
      case TypeSignature(tysig)         => occursInIntersection(x, tysig)
      case TypeSelection(Path(y, _), _) => x == y
    }


  def occursInIntersection(x : String, tysig : Intersection[Type]) : Boolean =
    tysig match {
      case Intersection(tys, phi, decls) =>
        val bI = tys.exists(occursInType(x, _));
        val bD = if (x == phi) false else decls.exists(occursInDecl(x, _));
        bI || bD
    }


  def occursInDecl(x : String, decl : Declaration) : Boolean =
    decl match {
      case DeclForValueLabel(_, vd) =>
        vd match {
          case DeclVal(_, ty, astopt) =>
            occursInType(x, ty) || astopt.map(occursInAst(x, _)).getOrElse(false)

          case DeclDef(_, params, tyans, astopt) =>
            /* `bName`: whether the list of parameters contains a variable having the same name as `x`
               `bOccur`: whether `x` occurs in some of the types of the parameters
             */
            val (bName, bOccur) = {
              params.foldLeft((false, false)){ case ((bName, bOccur), (y, ty)) =>
                (bName || x == y, bOccur || occursInType(x, ty))
              }
            };
            if (bName) {
              bOccur
            } else {
              astopt match {
                case None      => bOccur
                case Some(ast) => bOccur || occursInAst(x, ast)
              }
            }
        }

      case DeclForTypeLabel(_, td) =>
        td match {
          case DeclType(_, tyopt)  => tyopt.map(occursInType(x, _)).getOrElse(false)
          case DeclTrait(_, tysig) => occursInIntersection(x, tysig)
        }
    }


  def occursInAst(x : String, ast : Ast) : Boolean =
    ast match {
      case ValNewIn(y, ty, ast0)  => if (y == x) false else { occursInType(x, ty) || occursInAst(x, ast0) }
      case Var(y)                 => y == x
      case Access(ast0, _)        => occursInAst(x, ast0)
      case Call(ast0, _, astargs) => occursInAst(x, ast0) || astargs.exists(occursInAst(x, _))
    }


  def expandType(store : Store, tyenv : TypeEnv, x : String, ty : Type) : Either[TypeError, MapPair] =
    ty match {
      case TypeSelection(path, tlabel) =>
        typeMembership(store, tyenv, SingletonType(path), tlabel) flatMap { td =>
          td match {
            case DeclType(_, None) =>
              Left(NonEmbodiedTypeLabel(tlabel))

            case DeclType(did, Some(tyT)) =>
              if (store.contains(did)) {
                Left(AlreadySeen(did))
              } else {
                expandType(store.add(did), tyenv, x, tyT)
              }

            case DeclTrait(did, tysig) =>
              if (store.contains(did)) {
                Left(AlreadySeen(did))
              } else {
                val tysub : Type = TypeSignature(tysig)
                  /* TEMPORARY: should rename variables by using `phi` and `x` */
                expandType(store.add(did), tyenv, x, tysub)
              }
          }
        }

      case SingletonType(path) =>
        Left(CannotExpandSingletonType(path))

      case TypeSignature(Intersection(tys, phi, decls)) =>
        val init : Either[TypeError, MapPair] = Right(new EmptyMapPair())
        tys.foldLeft(init) { (acc, ty) =>
          acc flatMap { mapPairAcc =>
            expandType(store, tyenv, x, ty) flatMap { mapPair =>
              Right(mapPairAcc.concat(mapPair))
            }
          }
        } flatMap { mapPairMs =>
          val mapPairN = new MapPairOfDeclarations(decls)
          Right(mapPairMs.concat(mapPairN))
        }
    }


  def checkTypeWellFormedness(store : Store, tyenv :TypeEnv, ty : Type) : Either[TypeError, Unit] =
    ty match {
      case SingletonType(path) =>
        typeCheckPath(store, tyenv, path) flatMap { tyT =>
          extendStoreByPath(store, tyenv, path) flatMap { store =>
            checkTypeWellFormedness(store, tyenv, tyT)
          }
        }

      case TypeSelection(path, tlabel) =>
        typeMembership(store, tyenv, SingletonType(path), tlabel) flatMap { td =>
          td match {
            case DeclTrait(_, _) =>
              Right(Unit)

            case DeclType(did, tyTopt) =>
              tyTopt match {
                case None =>
                  Right(Unit)

                case Some(tyT) =>
                  if (store.contains(did)) {
                    Left(AlreadySeen(did))
                  } else {
                    checkTypeWellFormedness(store.add(did), tyenv, tyT)
                  }
              }
          }
        }

      case TypeSignature(tysig) =>
        ???
    }


  def isSubtype(store : Store, tyenv : TypeEnv, ty1 : Type, ty2 : Type) : Either[TypeError, Unit] =
    ???


  def pathOfAstIfPossible(ast : Ast) : Option[Path] = {
    def aux(vlabelacc : List[String], ast : Ast) : Option[Path] = {
      ast match {
        case Access(ast0, vlabel) => aux(vlabel :: vlabelacc, ast0)
        case Var(x)               => Some(Path(x, vlabelacc.reverse))
        case _                    => None
      }
    };
    aux(Nil, ast)
  }


  def separateLastLabel(path : Path) : Either[String, (Path, String)] =
    path match { case Path(x, vlabels) =>
      vlabels.reverse match {
        case Nil                   => Left(x)
        case vlabelLast :: revTail => Right((Path(x, revTail.reverse), vlabelLast))
      }
    }


  def typeCheckPath(store : Store, tyenv : TypeEnv, path : Path) : Either[TypeError, Type] =
    separateLastLabel(path) match {
      case Left(x) =>
        tyenv.findVariable(x) match {
          case None     => Left(UndefinedVariable(x))
          case Some(ty) => Right(ty)
        }

      case Right((pathRest, vlabel)) =>
        valueMembership(store, tyenv, SingletonType(pathRest), vlabel) flatMap {
          case DeclVal(_, ty, _)   => Right(ty)
          case DeclDef(_, _, _, _) => Left(TypeNotAFieldButAMethod(vlabel))
        }
    }


  def valueMembership(store : Store, tyenv : TypeEnv, ty : Type, vlabel : String) : Either[TypeError, ValueDeclBody] =
    members(store, tyenv, ty) flatMap { mapPair =>
      mapPair.getValue(vlabel) match {
        case None     => Left(ValueNotFound(vlabel))
        case Some(vd) => Right(vd)
      }
    }


  def typeMembership(store : Store, tyenv : TypeEnv, ty : Type, tlabel : String) : Either[TypeError, TypeDeclBody] =
    members(store, tyenv, ty) flatMap { mapPair =>
      mapPair.getType(tlabel) match {
        case None     => Left(TypeNotFound(tlabel))
        case Some(td) => Right(td)
      }
    }


  def members(store : Store, tyenv : TypeEnv, ty : Type) : Either[TypeError, MapPair] = {
    val phi : String = generateFreshVariable();
    ty match {
      case SingletonType(pathP) =>
        expandPathAlias(store, tyenv, pathP) flatMap { case (pathQ, tyT) =>
          extendStoreByPath(store, tyenv, pathP) flatMap { store =>
            expandType(store, tyenv, phi, tyT)
          }
        }

      case _ =>
        expandType(store, tyenv, phi, ty)
    }
  }


  def expandPathAlias(store : Store, tyenv : TypeEnv, pathP : Path) : Either[TypeError, (Path, Type)] =
    typeCheckPath(store, tyenv, pathP) flatMap { ty =>
      ty match {
        case SingletonType(pathQ) =>
          extendStoreByPath(store, tyenv, pathQ) flatMap { store =>
            expandPathAlias(store, tyenv, pathQ)
          }

        case _ =>
          Right((pathP, ty))
      }
    }


  def extendStoreByPath(store : Store, tyenv : TypeEnv, path : Path) : Either[TypeError, Store] =
    separateLastLabel(path) match {
      case Left(x) =>
        Right(store)

      case Right((pathP, vlabel)) =>
        valueMembership(store, tyenv, SingletonType(pathP), vlabel) flatMap { vd =>
          vd match {
            case DeclVal(did, _, _) =>
              if (store.contains(did)) {
                Left(AlreadySeen(did))
              } else {
                Right(store.add(did))
              }

            case DeclDef(_, _, _, _) =>
              Left(TypeNotAFieldButAMethod(vlabel))
          }
        }
    }
}
