//#include <iostream>

#include "anydsl/util/box.h"
#include "anydsl/util/types.h"
#include "anydsl/util/ops.h"
#include "anydsl/util/cast.h"
#include "anydsl/util/location.h"

using namespace anydsl;

struct A {
    virtual ~A() {}
};

struct B : public  A {
};

struct C : public  A {
};

int main() {
    std::cout << Location(Position("aaa", 23, 42), Position("bbb", 101, 666)) << std::endl;
    std::cout << Location(Position("aaa", 23, 42), Position("aaa", 101, 666)) << std::endl;
    std::cout << Location(Position("aaa", 23, 42), Position("aaa", 23, 666)) << std::endl;
    std::cout << Location(Position("aaa", 23, 42), Position("aaa", 23, 42)) << std::endl;

    std::cout << std::endl;

    std::cout << Location("aaa:23 col 42 - bbb:101 col 666") << std::endl;
    std::cout << Location("aaa:23 col 42 - 101 col 666") << std::endl;
    std::cout << Location("aaa:23 col 42 - 666") << std::endl;
    std::cout << Location("aaa:23 col 42") << std::endl;

    std::cout << std::endl;

    std::cout << "+" << std::endl;
    std::cout << u1(false) + u1(false) << std::endl;
    std::cout << u1(true) + u1(false) << std::endl;
    std::cout << u1(false) + u1(true) << std::endl;
    std::cout << u1(true) + u1(true) << std::endl;

    std::cout << "*" << std::endl;
    std::cout << u1(false) * u1(false) << std::endl;
    std::cout << u1(true) * u1(false) << std::endl;
    std::cout << u1(false) * u1(true) << std::endl;
    std::cout << u1(true) * u1(true) << std::endl;

    std::cout << "^" << std::endl;
    std::cout << (u1(false) ^ u1(false)) << std::endl;
    std::cout << (u1(true) ^ u1(false)) << std::endl;
    std::cout << (u1(false) ^ u1(true)) << std::endl;
    std::cout << (u1(true) ^ u1(true)) << std::endl;

    {
        std::cout << "+=" << std::endl;
        u1 u(false);
        std::cout << u << std::endl;
        u += 1;
        std::cout << u << std::endl;
        u += 1;
        std::cout << u << std::endl;
    }

    {
        std::cout << "pre ++" << std::endl;
        u1 u(false);
        std::cout << u << std::endl;
        ++u;
        std::cout << u << std::endl;
        ++u;
        std::cout << u << std::endl;
    }

    return 0;
}

bool foo(unsigned a, unsigned b) { 
    return anydsl::cmp_sgt(a, b).get();
}
