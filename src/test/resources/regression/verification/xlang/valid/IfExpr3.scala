/* Copyright 2009-2013 EPFL, Lausanne */

object IfExpr1 {

  def foo(a: Int): Int = {

    if(a > 0) {
      var a = 1
      var b = 2
      a = 3
      a + b
    } else {
      5
      //var a = 3
      //var b = 1
      //b = b + 1
      //a + b
    }
  } ensuring(_ == 5)

}
