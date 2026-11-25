/**
 * verify.cpp
 * @author kisslune 
 */

#include "Z3Mgr.h"

using namespace z3;
using namespace SVF;


/* A simple example

int main() {
    int* p;
    int q;
    int* r;
    int x;

    p = malloc();
    q = 5;
    *p = q;
    x = *p;
    assert(x==5);
}
*/
void Z3Tests::test0()
{
    //  int* p;
    expr p = getZ3Expr("p");
    //  int q;
    expr q = getZ3Expr("q");
    //  int* r;
    expr r = getZ3Expr("r");
    //  int x;
    expr x = getZ3Expr("x");
    //  p = malloc();
    addToSolver(p == getMemObjAddress("malloc"));
    //  q = 5;
    addToSolver(q == 5);
    //  *p = q;
    storeValue(p, q);
    //  x = *p;
    addToSolver(x == loadValue(p));

    // print the expression values
    printExprValues();

    addToSolver(x == getZ3Expr(10));
    // print the result of satisfiability check
    std::cout << solver.check() << std::endl;
}


/*
// Simple integers

    int main() {
        int a;
        int b;
        a = 0;
        b = a + 1;
        assert(b > 0);
    }
*/
void Z3Tests::test1()
{
    /// TODO: your code starts from here
    resetSolver();
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    addToSolver(a == 0);
    addToSolver(b == a + 1);

    if (solver.check() != sat || !checkNegateAssert(b > 0))
        throw z3::exception("test1: could not prove b > 0");
    std::cout << "test1: PASS\n";
}

/*
  // One-level pointers

    int main() {
        int* p;
        int q;
        int b;
        p = malloc;
        *p = 0;
        q = *p;
        *p = 3;
        b = *p + 1;
        assert(b > 3);
    }
*/
void Z3Tests::test2()
{
    /// TODO: your code starts from here
    resetSolver();
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr b = getZ3Expr("b");
    addToSolver(p == getMemObjAddress("malloc"));
    storeValue(p, getZ3Expr(0));
    addToSolver(q == loadValue(p));
    storeValue(p, getZ3Expr(3));
    addToSolver(b == loadValue(p) + 1);

    if (solver.check() != sat || !checkNegateAssert(b > 3))
        throw z3::exception("test2: could not prove b > 3");
    std::cout << "test2: PASS\n";
}

/*
    // Mutiple-level pointers

    int main() {
        int** p;
        int* q;
        int* r;
        int x;

        p = malloc1(..);
        q = malloc2(..);
        *p = q;
        *q = 10;
        r = *p;
        x = *r;
        assert(x==10);
    }
*/
void Z3Tests::test3()
{
    /// TODO: your code starts from here
    resetSolver();
    expr p = getZ3Expr("p");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr x = getZ3Expr("x");
    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(q == getMemObjAddress("malloc2"));
    storeValue(p, q);
    storeValue(q, getZ3Expr(10));
    addToSolver(r == loadValue(p));
    addToSolver(x == loadValue(r));

    if (solver.check() != sat || !checkNegateAssert(x == 10))
        throw z3::exception("test3: could not prove x == 10");
    std::cout << "test3: PASS\n";
}

/*
   // Array and pointers

    int main() {
        int* p;
        int* x;
        int* y;
        int a;
        int b;
        p = malloc;
        x = &p[0];
        y = &p[1]
        *x = 10;
        *y = 11;
        a = *x;
        b = *y;
        assert((a + b)>20);
    }
*/
void Z3Tests::test4()
{
    /// TODO: your code starts from here
    resetSolver();
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    addToSolver(p == getMemObjAddress("malloc"));
    addToSolver(x == getGepObjAddress(p, 0));
    addToSolver(y == getGepObjAddress(p, 1));
    storeValue(x, getZ3Expr(10));
    storeValue(y, getZ3Expr(11));
    addToSolver(a == loadValue(x));
    addToSolver(b == loadValue(y));

    if (solver.check() != sat || !checkNegateAssert(a + b > 20))
        throw z3::exception("test4: could not prove a + b > 20");
    std::cout << "test4: PASS\n";
}

/*
    // Branches

int main(int argv) {
    int a;
    int b;
    int b1;
    a = argv + 1;
    b = 5;
    if(a > 10)
        b = a;
    b1 = b;
    assert(b1 >= 5);
}
*/
void Z3Tests::test5()
{
    /// TODO: your code starts from here
    resetSolver();
    expr argv = getZ3Expr("argv");
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr b1 = getZ3Expr("b1");
    addToSolver(a == argv + 1);
    addToSolver(b == 5);
    addToSolver(b1 == ite(a > 10, a, b));

    if (solver.check() != sat || !checkNegateAssert(b1 >= 5))
        throw z3::exception("test5: could not prove b1 >= 5");
    std::cout << "test5: PASS\n";
}

/*
// Compare and pointers
int main() {
   int *a = malloc1;
   int *b = malloc2;
   *a = 5;
   *b = 10;
   int *p;
   if (*a < *b) {
       p = a;
   } else {
       p = b;
   }
   assert(*p == 5);
}
*/
void Z3Tests::test6()
{
    /// TODO: your code starts from here
    resetSolver();
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr p = getZ3Expr("p");
    addToSolver(a == getMemObjAddress("malloc1"));
    addToSolver(b == getMemObjAddress("malloc2"));
    storeValue(a, getZ3Expr(5));
    storeValue(b, getZ3Expr(10));
    addToSolver(p == ite(loadValue(a) < loadValue(b), a, b));
    expr pointee = loadValue(p);

    if (solver.check() != sat || !checkNegateAssert(pointee == 5))
        throw z3::exception("test6: could not prove *p == 5");
    std::cout << "test6: PASS\n";
}

/*
 int main() {
	int a = 1, b = 2, c = 3;
	int d;
  if (a > 0) {
  	d = b + c;
  }
  else {
  	d = b - c;
  }
  assert(d == 5);
 }
 */
void Z3Tests::test7()
{
    /// TODO: your code starts from here
    resetSolver();
    expr a = getZ3Expr("a");
    expr b = getZ3Expr("b");
    expr c = getZ3Expr("c");
    expr d = getZ3Expr("d");
    addToSolver(a == 1);
    addToSolver(b == 2);
    addToSolver(c == 3);
    addToSolver(d == ite(a > 0, b + c, b - c));

    if (solver.check() != sat || !checkNegateAssert(d == 5))
        throw z3::exception("test7: could not prove d == 5");
    std::cout << "test7: PASS\n";
}

/*
 int main() {
    int arr[2] = {0, 1};
    int a = 10;
    int *p;
    if (a > 5) {
        p = &arr[0];
    }
    else {
        p = &arr[1];
    }
    assert(*p == 0);
 }
 */
void Z3Tests::test8()
{
    /// TODO: your code starts from here
    resetSolver();
    expr arr = getZ3Expr("arr");
    expr a = getZ3Expr("a");
    expr p = getZ3Expr("p");
    addToSolver(arr == getMemObjAddress("array"));
    expr first = getGepObjAddress(arr, 0);
    expr second = getGepObjAddress(arr, 1);
    storeValue(first, getZ3Expr(0));
    storeValue(second, getZ3Expr(1));
    addToSolver(a == 10);
    addToSolver(p == ite(a > 5, first, second));
    expr pointee = loadValue(p);

    if (solver.check() != sat || !checkNegateAssert(pointee == 0))
        throw z3::exception("test8: could not prove *p == 0");
    std::cout << "test8: PASS\n";
}

/*
    // Struct and pointers

    struct A{ int f0; int* f1;};
    int main() {
       struct A* p;
       int* x;
       int* q;
       int** r;
       int* y;
       int z;

       p = malloc1;
       x = malloc2;
       *x = 5;
       q = &(p->f0);
       *q = 10;
       r = &(p->f1);
       *r = x;
       y = *r;
       z = *q + *y;
       assert(z == 15);
    }
*/
void Z3Tests::test9()
{
    /// TODO: your code starts from here
    resetSolver();
    expr p = getZ3Expr("p");
    expr x = getZ3Expr("x");
    expr q = getZ3Expr("q");
    expr r = getZ3Expr("r");
    expr y = getZ3Expr("y");
    expr z = getZ3Expr("z");
    addToSolver(p == getMemObjAddress("malloc1"));
    addToSolver(x == getMemObjAddress("malloc2"));
    storeValue(x, getZ3Expr(5));
    addToSolver(q == getGepObjAddress(p, 0));
    storeValue(q, getZ3Expr(10));
    addToSolver(r == getGepObjAddress(p, 1));
    storeValue(r, x);
    addToSolver(y == loadValue(r));
    addToSolver(z == loadValue(q) + loadValue(y));

    if (solver.check() != sat || !checkNegateAssert(z == 15))
        throw z3::exception("test9: could not prove z == 15");
    std::cout << "test9: PASS\n";
}

/*
int foo(int z) {
    k = z;
    return k;
}
int main() {
  int x;
  int y;
  y = foo(2);
  x = foo(3);
  assert(x == 3 && y == 2);
}
*/
void Z3Tests::test10()
{
    /// TODO: your code starts from here
    resetSolver();
    expr x = getZ3Expr("x");
    expr y = getZ3Expr("y");
    // Give the formal argument and local variable distinct names at each call site.
    auto foo = [&](const expr& argument, const std::string& callSite)
    {
        expr z = getZ3Expr(callSite + "_z");
        expr k = getZ3Expr(callSite + "_k");
        addToSolver(z == argument);
        addToSolver(k == z);
        return k;
    };
    addToSolver(y == foo(getZ3Expr(2), "foo_call1"));
    addToSolver(x == foo(getZ3Expr(3), "foo_call2"));

    if (solver.check() != sat || !checkNegateAssert(x == 3 && y == 2))
        throw z3::exception("test10: could not prove x == 3 && y == 2");
    std::cout << "test10: PASS\n";
}


int main()
{
    Z3Tests tests;
    tests.test0();
    tests.solver.reset();
    tests.test1();
    tests.solver.reset();
    tests.test2();
    tests.solver.reset();
    tests.test3();
    tests.solver.reset();
    tests.test4();
    tests.solver.reset();
    tests.test5();
    tests.solver.reset();
    tests.test6();
    tests.solver.reset();
    tests.test7();
    tests.solver.reset();
    tests.test8();
    tests.solver.reset();
    tests.test9();
    tests.solver.reset();
    tests.test10();

    return 0;
}