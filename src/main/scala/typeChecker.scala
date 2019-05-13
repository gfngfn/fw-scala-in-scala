
sealed trait TypeError
case class TypeNotAFieldButAMethod(vl : String)           extends TypeError
case class TypeNotAMethodButAField(vl : String)           extends TypeError
case class TypeWrongNumberOfArguments(la : Int, lp : Int) extends TypeError


class Store {}  // TEMPORARY
class TypeEnv {}  // TEMPORARY


object FWSTypeChecker {

  def typeCheck(store : Store, tyenv : TypeEnv, ast : Ast) : Either[TypeError, Type] =
    ast match {
      case Access(ast0, vlabel) =>
        pathOfAstIfPossible(ast0) match {
          case None =>
          /* -- if the expression 'ast0' is not (interprettable as) a path -- */
            typeCheck(store, tyenv, ast0) flatMap { ty0 =>
              membership(store, tyenv, ty0, vlabel) flatMap {
                case DeclVal(ty, _) =>
                  Right(ty)

                case DeclDef(_, _, _) =>
                  Left(TypeNotAFieldButAMethod(vlabel))
              }
            }

          case Some(path) =>
            val _ = typeCheckPath(store, tyenv, path);
            Right(SingletonType(path))
        }

      case Call(ast0, vlabel, astargs) =>
        typeCheck(store, tyenv, ast0) flatMap { ty0 =>
          membership(store, tyenv, ty0, vlabel) flatMap {
            case DeclVal(_, _) =>
              Left(TypeNotAMethodButAField(vlabel))

            case DeclDef(params, tyans, _) =>
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
        ???

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


  def isSubtype(store : Store, tyenv : TypeEnv, ty1 : Type, ty2 : Type) : Either[TypeError, Unit] =
    ???


  def pathOfAstIfPossible(ast : Ast) : Option[Path] =
    ???


  def typeCheckPath(store : Store, tyenv : TypeEnv, path : Path) : Either[TypeError, Type] =
    ???


  def membership(store : Store, tyenv : TypeEnv, ty : Type, vlabel : String) : Either[TypeError, ValueDeclBody] =
    ???
}
