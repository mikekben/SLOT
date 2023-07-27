#ifndef PAIR
#define PAIR std::pair<APInt,unsigned>
#endif

namespace SLOT
{
    inline APInt APMax(APInt left, APInt right)
    {
        //Have to have same width for comparison
        APInt nl = left;
        APInt nr = right;
        if (left.getBitWidth() > right.getBitWidth())
        {
            nr = right.zext(left.getBitWidth());
        }
        else if (left.getBitWidth() < right.getBitWidth())
        {
            nl = left.zext(right.getBitWidth());
        }

        return nl.ult(nr) ? nr : nl;
    }

    inline APInt APPlus(APInt left, APInt right)
    {
        //Add one bit and use the wider
        unsigned newWidth = std::max(left.getBitWidth() + 1, right.getBitWidth() + 1);
        APInt nl = left.zext(newWidth);
        APInt nr = right.zext(newWidth);

        APInt val = nl + nr;
        if (val.countLeadingZeros() > 0)
        {
            val = val.trunc((newWidth-val.countLeadingZeros())+1);
        }

        return val;
    }

    inline APInt APMult(APInt left, APInt right)
    {
        //Add the bits together
        unsigned newWidth = left.getBitWidth() + right.getBitWidth();
        APInt nl = left.zext(newWidth);
        APInt nr = right.zext(newWidth);

        APInt val = nl * nr;
        if (val.countLeadingZeros() > 0)
        {
            val = val.trunc((newWidth-val.countLeadingZeros())+1);
        }

        return val;
    }

    inline APInt APDiv(APInt left, APInt right)
    {
        //Have to have same width for division
        APInt nl = left;
        APInt nr = right;
        if (left.getBitWidth() > right.getBitWidth())
        {
            nr = right.zext(left.getBitWidth());
        }
        else if (left.getBitWidth() < right.getBitWidth())
        {
            nl = left.zext(right.getBitWidth());
        }

        APInt val = nl.udiv(nr);
        if (val.countLeadingZeros() > 0)
        {
            val = val.trunc((val.getBitWidth()-val.countLeadingZeros())+1);
        }

        return val;
    }


    inline PAIR PairMax(PAIR left, PAIR right)
    {
        return {APMax(left.first,right.first), (left.second > right.second) ? left.second : right.second};
    }

    inline PAIR PairPlus(PAIR left, PAIR right)
    {
        return {APPlus(left.first,right.first), (left.second > right.second) ? left.second : right.second};
    }

    inline PAIR PairMult(PAIR left, PAIR right)
    {
        return {APMult(left.first,right.first), left.second + right.second};
    }

    inline PAIR PairDiv(PAIR left, PAIR right)
    {
        //This is the source of underapproximation :(
        return {APDiv(left.first,right.first), left.second + right.second};
    }
    
}