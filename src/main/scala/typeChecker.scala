
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
case class ShouldNotBeASingletonType()                     extends TypeError
case class InvalidDefOverriding(vl : String)               extends TypeError
case class InvalidTypeOverriding(vl : String)              extends TypeError


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
              /* (\preccurly-TYPE) */
                expandType(store.add(did), tyenv, x, tyT)
              }

            case DeclTrait(did, tysig) =>
              if (store.contains(did)) {
                Left(AlreadySeen(did))
              } else {
              /* (\preccurly-CLASS) */
                val tysub : Type = TypeSignature(tysig)
                  /* TEMPORARY: should rename variables by using `phi` and `x` */
                expandType(store.add(did), tyenv, x, tysub)
              }
          }
        }

      case SingletonType(path) =>
        Left(CannotExpandSingletonType(path))

      case TypeSignature(Intersection(tys, phi, decls)) =>
      /* (\preccurly-SIGNATURE) */
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
      /* (WF-SINGLETON) */
        typeCheckPath(store, tyenv, path) flatMap { tyT =>
          extendStoreByPath(store, tyenv, path) flatMap { store =>
            checkTypeWellFormedness(store, tyenv, tyT)
          }
        }

      case TypeSelection(path, tlabel) =>
        typeMembership(store, tyenv, SingletonType(path), tlabel) flatMap { td =>
          td match {
            case DeclTrait(_, _) =>
            /* (WF-CLASS) */
              Right(Unit)

            case DeclType(did, tyTopt) =>
            /* (WF-TYPE) */
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
      /* (WF-SIGNATURE) */
        tysig match { case Intersection(_, phi, _) =>
          checkMemberWellFormedness(store, tyenv.add(phi, ty), tysig, phi)
        }
    }


  def checkMemberWellFormedness(store : Store, tyenv : TypeEnv, tysig : Intersection[Type], x : String) : Either[TypeError, Unit] =
    /* (WF-X-SIGNATURE) */
    /* FIXME; should perform alpha-renaming as to `x` and `phi` */
    tysig match { case Intersection(tyTs, phi, declsM) =>
      val resInit : Either[TypeError, Unit] = Right(())
      declsM.foldLeft(resInit) { case (res, decl) =>
        res flatMap { _ =>
          checkMemberWellFormednessSub(store, tyenv, decl, phi)
        }
      } flatMap { _ =>
        val resInit : Either[TypeError, List[MapPair]] = Right(Nil)
        tyTs.foldLeft(resInit) { case (res, tyT) =>
          res flatMap { acc =>
            expandType(store, tyenv, phi, tyT) flatMap { mapPairN =>
              Right(mapPairN :: acc)
            }
          }
        } flatMap { (mapPairNRev : List[MapPair]) =>
          val mapPairNs : List[MapPair] = mapPairNRev.reverse
          val mapPairM : MapPair = new MapPairOfDeclarations(declsM)
          def aux(mapPairNs : List[MapPair]) : Either[TypeError, Unit] = {
            mapPairNs match {
              case Nil =>
                Right(())

              case mapPairN :: rest =>
                checkOverrideWellFormedness(store, tyenv, mapPairM, mapPairN, rest) flatMap { _ =>
                  aux(rest)
                }
            }
          }
          aux(mapPairNs)
        }
      }
    }


  def checkOverrideWellFormedness(store : Store, tyenv : TypeEnv, mapPairM : MapPair, mapPairNi : MapPair, rest : List[MapPair]) : Either[TypeError, Unit] = {
    val resInit : Either[TypeError, Unit] = Right(())
    rest.foldLeft(resInit) { case (res, mapPairNij) =>
      res flatMap { _ =>
        isPointwiseSubtype(store, tyenv, mapPairNij.concat(mapPairM), mapPairNi)
      }
    }
  }


  def isPointwiseSubtype(store : Store, tyenv : TypeEnv, mapPair1 : MapPair, mapPair2 : MapPair) : Either[TypeError, Unit] ={
    /* \ll */
    val resInit : Either[TypeError, Unit] = Right(())
    mapPair1.foldValueIntersection[Either[TypeError, Unit]](mapPair2, resInit, { case (res, vlabel, vd1, vd2) =>
      res flatMap { _ =>
        isValueMemberSubtype(store, tyenv, vlabel, vd1, vd2)
      }
    }) flatMap { _ =>
      mapPair1.foldTypeIntersection[Either[TypeError, Unit]](mapPair2, resInit, { case (res, tlabel, td1, td2) =>
        res flatMap { _ =>
          isTypeMemberSubtype(store, tyenv, tlabel, td1, td2)
        }
      })
    }
  }


  def isValueMemberSubtype(store : Store, tyenv : TypeEnv, vlabel : String, vd1 : ValueDeclBody, vd2 : ValueDeclBody) : Either[TypeError, Unit] =
    (vd1, vd2) match {
      case (DeclVal(_, ty1, _), DeclVal(_, ty2, _)) =>
      /* (<:-MEMBER-FIELD) */
        isSubtype(store, tyenv, ty1, ty2)

      case (DeclDef(_, params1, tyans1, _), DeclDef(_, params2, tyans2, _)) =>
      /* (<:-MEMBER-METHOD) */
        if (params1.length != params2.length) {
          Left(InvalidDefOverriding(vlabel))
        } else {
          val pairs : List[((String, Type), (String, Type))] = params1.zip(params2)
          val resInit : Either[TypeError, Unit] = Right(())
          pairs.foldLeft(resInit) { case (res, ((_, ty1), (_, ty2))) =>
            isSubtype(store, tyenv, ty2, ty1)
              /* contravariant as to parameters */
          } flatMap { _ =>
            isSubtype(store, tyenv, tyans1, tyans2)
              /* covariant as to returned types */
          }
        }

      case _ =>
        Left(InvalidDefOverriding(vlabel))
    }


  def isTypeMemberSubtype(store : Store, tyenv : TypeEnv, tlabel : String, td1 : TypeDeclBody, td2 : TypeDeclBody) : Either[TypeError, Unit] =
    (td1, td2) match {
      case (DeclType(_, tyopt1), DeclType(_, tyopt2)) =>
        (tyopt1, tyopt2) match {
          case (Some(ty1), Some(ty2)) => ??? /* FIXME; should return whether `ty1` is equal to `ty2` */
          case (Some(_), None)        => Right(())
          case _                      => Left(InvalidTypeOverriding(tlabel))
        }

      case (DeclTrait(_, tysig1), DeclTrait(_, tysig2)) =>
        ??? /* FIXME; should return whether `tysig1` is equal to `tysig2` */

      case _ =>
        Left(InvalidTypeOverriding(tlabel))
    }


  def checkMemberWellFormednessSub(store : Store, tyenv : TypeEnv, decl : Declaration, x : String) : Either[TypeError, Unit] =
    decl match {
      case DeclForTypeLabel(tlabel, td) =>
        td match {
          case DeclType(_, tyopt) =>
          /* (WF-X-TYPE) */
            tyopt match {
              case None     => Right(())
              case Some(ty) => checkTypeWellFormedness(store, tyenv, ty)
            }

          case DeclTrait(_, tysig) =>
          /* (WF-X-CLASS) */
            tysig match { case Intersection(_, phi, _) =>
              val tyenvsub : TypeEnv = tyenv.add(phi, TypeSelection(Path(x, Nil), tlabel))
              checkMemberWellFormedness(store, tyenvsub, tysig, phi)
            }
        }

      case DeclForValueLabel(vlabel, vd) =>
        vd match {
          case DeclVal(_, tyT, astopt) =>
          /* (WF-X_FIELD) */
            checkTypeWellFormedness(store, tyenv, tyT) flatMap { _ =>
              astopt match {
                case None =>
                  Right(())

                case Some(ast) =>
                  typeCheck(store, tyenv, ast) flatMap { tyTprime =>
                    isSubtype(store, tyenv, tyTprime, tyT)
                  }
              }
            }

          case DeclDef(_, params, tyT, astopt) =>
          /* (WF-X_METHOD) */
            checkTypeWellFormedness(store, tyenv, tyT) flatMap { _ =>
              val resInit : Either[TypeError, TypeEnv] = Right(tyenv)
              params.foldLeft(resInit) { case (res, (y, tyS)) =>
                res flatMap { tyenv =>
                  tyS match {
                    case SingletonType(_) =>
                      Left(ShouldNotBeASingletonType())

                    case _ =>
                      checkTypeWellFormedness(store, tyenv, tyS) flatMap { _ =>
                        Right(tyenv.add(y, tyS))
                      }
                  }
                }
              } flatMap { tyenvsub =>
                astopt match {
                  case None =>
                    Right(())

                  case Some(ast) =>
                    typeCheck(store, tyenvsub, ast) flatMap { tyTprime =>
                      isSubtype(store, tyenv, tyTprime, tyT)
                        /* note: not `tyenvsub` but `tyenv` */
                    }
                }
              }
            }
        }
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
      /* (\ni-SINGLETON) */
        expandPathAlias(store, tyenv, pathP) flatMap { case (pathQ, tyT) =>
          extendStoreByPath(store, tyenv, pathP) flatMap { store =>
            expandType(store, tyenv, phi, tyT)
          }
        }

      case _ =>
      /* (\ni-OTHER) */
        expandType(store, tyenv, phi, ty)
    }
  }


  def expandPathAlias(store : Store, tyenv : TypeEnv, pathP : Path) : Either[TypeError, (Path, Type)] =
    typeCheckPath(store, tyenv, pathP) flatMap { ty =>
      ty match {
        case SingletonType(pathQ) =>
        /* (\cong-STEP) */
          extendStoreByPath(store, tyenv, pathQ) flatMap { store =>
            expandPathAlias(store, tyenv, pathQ)
          }

        case _ =>
        /* (\cong-REFL) */
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
