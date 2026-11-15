"""Exact rational checks on a finite synthetic timetable."""
from fractions import Fraction


def mass(indices):
    return sum((Fraction(1, 2 ** (e + 1)) for e in indices), Fraction())


def main():
    # None denotes no scheduled halt within this finite toy model.
    timetable = (None, 7, 0, 40, None, 2, 3, None)
    count = len(timetable)
    eventual = {e for e, time in enumerate(timetable) if time is not None}
    limit = mass(eventual)
    previous = Fraction()
    assert mass(range(count)) + Fraction(1, 2**count) == 1

    for stage in range(max(t for t in timetable if t is not None) + 1):
        seen = {e for e in eventual if timetable[e] <= stage}
        covered = mass(seen)
        risk = mass(eventual - seen)
        assert previous <= covered <= limit
        assert risk == limit - covered
        for e in eventual - seen:
            assert Fraction(1, 2 ** (e + 1)) <= risk
        previous = covered
    assert previous == limit

    for k in range(1, 9):
        stage = next(
            t for t in range(41)
            if mass(e for e in eventual if timetable[e] > t) < Fraction(1, 2**k)
        )
        for e in range(min(k, count)):
            assert (e in eventual) == (timetable[e] is not None and timetable[e] <= stage)
    print(f"Checked 41 stages and 8 tolerances with exact fractions. Eventual mass = {limit}.")


if __name__ == "__main__":
    main()
