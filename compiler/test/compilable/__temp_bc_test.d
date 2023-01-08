int ret()
{
    enum A = 200;
    enum B = A / 100;

    int a = 1;
    int b = a * 2;
    int c;
    c = b + ret2() + c;

    int nested()
    {
        a = 2;
        return a * 100;
    }

    return (c / f(2) + (B - 3)) + nested() + a;

    // int a = 2;

    // {
    //     int b = 100;
    // }

    // {
    //     int b = 200;
    // }

    // int b = a;

    // return b;
}

int ret2()
{
    int a = 200;
    return a;
}

int f(int a)
{
    return a;
}

void main()
{
    enum a = ret();
    pragma(msg, a);
}

void side(int a)
{
    a += 3;
}