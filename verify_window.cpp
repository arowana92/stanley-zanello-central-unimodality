// Certify upper-half strict log-concavity using the window in rising-window.md.
// certified-window.md proves the relative error bound for the arithmetic below.
#include <algorithm>
#include <cfenv>
#include <cmath>
#include <cstdint>
#include <functional>
#include <iostream>
#include <limits>
#include <stdexcept>
#include <string>
#include <vector>

#ifdef __FAST_MATH__
#error "Use IEEE arithmetic without fast-math"
#endif
static_assert(std::numeric_limits<double>::is_iec559 &&
              std::numeric_limits<double>::digits == 53 &&
              std::numeric_limits<double>::radix == 2);

int window_end(int length) {
    const std::int64_t squared = 4LL * length * length * length;
    std::int64_t k = static_cast<std::int64_t>(std::sqrt(static_cast<double>(squared)));
    while (k*k > squared) --k;
    while ((k+1)*(k+1) <= squared) ++k;
    return static_cast<int>(k);
}

int min_area(int height) {
    return height * height / 4;
}

void enumerate(int length, int row, int previous, int rank,
               std::vector<std::uint64_t>& ranks) {
    ++ranks[rank];
    const int largest = std::min(previous-1, length-1-2*row);
    for (int part = 1; part <= largest; ++part) {
        enumerate(length, row+1, part, rank+part, ranks);
    }
}

void check_direct(int length, const std::vector<double>& row, double unit) {
    const int degree = length*length/4;
    std::vector<std::uint64_t> ranks(degree+1, 0);
    enumerate(length, 0, length, 0, ranks);
    for (int k = 0; k <= degree; ++k) {
        if (row[k] != unit * static_cast<double>(ranks[degree-k])) {
            throw std::runtime_error("direct count differs at length " + std::to_string(length));
        }
    }
    const auto peak = std::max_element(ranks.begin(), ranks.end());
    if (!std::is_sorted(ranks.begin(), peak+1) ||
        !std::is_sorted(peak, ranks.end(), std::greater<std::uint64_t>())) {
        throw std::runtime_error("direct row is not unimodal at length " + std::to_string(length));
    }
}

void certify(int max_n) {
    if (std::fegetround() != FE_TONEAREST) throw std::runtime_error("rounding mode");
    if (max_n < 12 || max_n > 1019) throw std::invalid_argument("require 12 <= max_n <= 1019");
    const int last = 2*max_n+1;
    const int cap = std::max(25*25/4, window_end(last)+1);
    const double unit = std::ldexp(1.0, -max_n);
    std::vector<std::vector<double>> heights;
    for (int h = 0; h <= last && min_area(h) <= cap; ++h) {
        heights.emplace_back(cap-min_area(h)+1, 0.0);
    }
    heights[0][0] = unit;
    const int highest = static_cast<int>(heights.size())-1;
    std::int64_t checked = 0;
    for (int t = 1; t <= last; ++t) {
        const int degree = t*t/4;
        // Each height reads only the opposite parity, still at time t-1.
        for (int h = t%2; h <= std::min(t, highest); h += 2) {
            const int downs = (t-h)/2;
            const int end = std::min(cap, degree-downs*(downs+1)/2)-min_area(h)+1;
            auto& dest = heights[h];
            const int shift = std::min(h, end);
            if (h == 0) {
                std::copy_n(heights[1].begin(), end, dest.begin());
            } else if (h == highest) {
                std::copy_n(heights[h-1].begin(), end, dest.begin());
            } else {
                const auto& up = heights[h-1];
                const auto& down = heights[h+1];
                std::copy_n(up.begin(), shift, dest.begin());
                for (int i = shift; i < end; ++i) dest[i] = up[i] + down[i-h];
            }
        }
        if (t < 2) continue;
        const int stop = std::min(degree/2, window_end(t));
        const int last_corank = (t <= 25) ? degree : stop+1;
        std::vector<double> row(last_corank+1, 0.0);
        for (int h = t%2; h <= std::min(t, highest); h += 2) {
            const int first = min_area(h);
            for (int k = first; k <= last_corank; ++k) row[k] += heights[h][k-first];
        }
        if (t <= 25) check_direct(t, row, unit);
        if (t/2 < 9) continue;
        double left_ratio = row[1]/row[0];
        for (int k = 1; k <= stop; ++k) {
            const double right_ratio = row[k+1]/row[k];
            if (!std::isnormal(left_ratio) || !std::isnormal(right_ratio) ||
                !(left_ratio > right_ratio*(1.0+0x1p-36))) {
                throw std::runtime_error("uncertified ratio at length " + std::to_string(t) +
                                         ", corank " + std::to_string(k));
            }
            left_ratio = right_ratio;
            ++checked;
        }
        if (t % 256 == 0) std::cout << "Verified through word length " << t << std::endl;
    }
    std::cout << "Certified " << checked << " strict determinants in both families for 9 <= n <= "
              << max_n << ". Direct counts agree through n = 12." << std::endl;
}

int main(int argc, char** argv) {
    try {
        if (argc > 2) throw std::invalid_argument("usage: verify_window [max_n]");
        certify(argc == 2 ? std::stoi(argv[1]) : 1000);
    } catch (const std::exception& error) {
        std::cerr << error.what() << std::endl;
        return 1;
    }
}
