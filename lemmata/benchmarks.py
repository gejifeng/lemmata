"""Problem sets used in the experiments reported in README.md."""

# The 13 PutnamBench problems used to develop and evaluate the original pipeline.
MAIN_SET = [
    "putnam_2001_a1", "putnam_1992_a1", "putnam_1966_a1", "putnam_1993_a2", "putnam_1963_a2",
    "putnam_1965_b5", "putnam_1999_a2", "putnam_1969_a2", "putnam_2000_a4", "putnam_1962_a1",
    "putnam_1964_a1", "putnam_1965_a1", "putnam_1976_b3",
]

# 20 additional, mostly elementary PutnamBench problems (number theory, algebra, combinatorics),
# hand-picked among the shortest statements, used for fast A/B comparisons.
EASY_SET = [
    "putnam_1972_a5", "putnam_1968_a1", "putnam_2000_b2", "putnam_1969_b1", "putnam_2000_b4", "putnam_1977_a5",
    "putnam_1972_b3", "putnam_1966_b2", "putnam_1988_b1", "putnam_1978_a1", "putnam_2000_a2", "putnam_1965_b3",
    "putnam_1974_b3", "putnam_1989_a3", "putnam_2004_b2", "putnam_1991_b4", "putnam_1983_a4", "putnam_1973_b2",
    "putnam_2001_a5", "putnam_1970_a4",
]

SETS = {"main": MAIN_SET, "easy": EASY_SET, "all": MAIN_SET + EASY_SET}
