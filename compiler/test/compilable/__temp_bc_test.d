int ret()
{
    return 1;
}

void main()
{
    enum a = 1 + 100;
    pragma(msg, a);
}

void side(int a)
{
    a += 3;
}