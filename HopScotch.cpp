#include <iostream>
#include <vector>
#include <random>
#include <algorithm>
#include <array>
#include <chrono>
#include <thread>
#include <unordered_map>
#include <unordered_set>
#pragma gcc target ("avx2")
#pragma gcc optimization ("o3")
#pragma gcc optimization ("unroll-loops")
#pragma comment(linker, "/stack:200000000")
#pragma gcc optimize("ofast")
#pragma gcc target("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,avx,tune=native")

#define molnia_makvin ios_base::sync_with_stdio(0); cout.tie(0); cin.tie(0);
std::chrono::time_point<std::chrono::system_clock> start_inside = std::chrono::system_clock::now();
std::chrono::time_point<std::chrono::system_clock> end_inside = std::chrono::system_clock::now();
std::chrono::duration<double> elapsed_seconds_inside = end_inside-start_inside;

template<typename T>
class HopScotch {
private:
    class Bucket {
    private:
        T value;
        bool in_use;
        long long original_index_of_value;
        std::vector<bool> bitmap;
    public:
        Bucket(long long max_distance) : in_use(false) {
            bitmap.resize(max_distance, false);
        }

        void setValue(const T& val, long long orig_index) {
            value = val;
            original_index_of_value = orig_index;
            in_use = true;
        }

        const T& getValue() const { return value; }

        long long getOriginalIndex() const { return original_index_of_value; }

        bool bitmapIsFull() const {
            return std::all_of(bitmap.begin(), bitmap.end(), [](bool b) { return b; });
        }

        bool getInUse() const { return in_use; }

        void turnOff() { in_use = false; }

        bool getBitmap(long long index) const { return bitmap[index]; }

        void setBitmap(long long index, bool set) { bitmap[index] = set; }

        void clearBitmap() {
            std::fill(bitmap.begin(), bitmap.end(), false);
        }

        void resize_max_dist(long long plus_index) {
            bitmap.resize(bitmap.size() + plus_index, false);
        }
    };

    long long ONLY_LEFT_TO_RIGHT = 0, ONLY_RIGHT_TO_LEFT = 0, LEFT_TO_RIGHT_IS_BETTER = 0, RIGHT_TO_LEFT_IS_BETTER = 0, RESIZE = 0, HOP_INCREMENTED = 0;
    long long max_dist;
    std::vector<Bucket> vct;

    void resize(std::vector<Bucket>* copy_from) {
        std::vector<Bucket> tmp;
        tmp.reserve(vct.size());
        for (auto& buck : vct) {
            if (buck.getInUse()) {
                tmp.emplace_back(buck);
            }
            buck.clearBitmap();
            buck.turnOff();
        }
        vct.reserve(vct.size() << 1);
        vct.resize((vct.size() - 1) << 1, Bucket(max_dist));
        for (Bucket& buck : tmp) {
            private_insert(buck.getValue(), &tmp);
        }
    }

    long long hashFunction(const T& val) const {
        long long size = vct.size();
        return (std::hash<T>{}(val) + size) % size;
    }

    bool checkMaxDistBoundsForSwap(long long swap_index, long long free_index) const {
        long long dist_border = vct[swap_index].getOriginalIndex() + max_dist - 1;
        return (swap_index < free_index && (vct.size() + dist_border) % vct.size() < free_index) ||
               (swap_index > free_index && (dist_border % vct.size() < free_index || dist_border == (dist_border % vct.size())));
    }

    bool checkIfInMaxDist(long long border_index, long long free_index) const {
        return !((border_index - max_dist < 0 && (free_index < border_index || free_index >= vct.size() + border_index - max_dist)) ||
                 (border_index - max_dist >= 0 && (free_index >= border_index - max_dist && free_index < border_index)));
    }

    long long leftToRightShift(long long free_index, bool is_virtual) {
        const long long border_index = free_index;
        long long activity_counter = 0;
        while (free_index != ((vct.size() + border_index - max_dist) % vct.size()) && vct[free_index].getInUse()) {
            free_index = (free_index + 1) % vct.size();
        }

        if (vct[free_index].getInUse()) { return -1; }

        while (checkIfInMaxDist(border_index, free_index)) {
            long long swap_index = (vct.size() + free_index - max_dist + 1) % vct.size();
            while (swap_index != free_index && checkMaxDistBoundsForSwap(swap_index, free_index)) {
                swap_index = (swap_index + 1) % vct.size();
            }
            if (swap_index == free_index) { return -1; }
            activity_counter++;
            if (!is_virtual) {
                long long swap_original_index = vct[swap_index].getOriginalIndex();
                vct[free_index].setValue(vct[swap_index].getValue(), swap_original_index);
                vct[swap_original_index].setBitmap((vct.size() + swap_index - swap_original_index) % vct.size(), false);
                vct[swap_original_index].setBitmap((vct.size() + free_index - swap_original_index) % vct.size(), true);
                vct[swap_index].turnOff();
            }
            free_index = swap_index;
        }
        return is_virtual ? activity_counter : free_index;
    }

    bool checkMaxDistBoundsForSwapForRightToLeftShift(long long swap_index, long long free_index) const {
        long long swap_original_index = vct[swap_index].getOriginalIndex();
        return (free_index < swap_index && (swap_original_index > free_index && swap_index >= swap_original_index)) ||
               (free_index > swap_index && ((swap_index >= swap_original_index && swap_original_index < free_index)
                                            || (swap_index < swap_original_index && swap_original_index > free_index)));
    }

    long long rightToLeftShift(const long long border_index, bool is_virtual) {
        long long free_index = (vct.size() + border_index - max_dist - 1) % vct.size();
        long long activity_counter = 0;
        while (free_index != border_index && vct[free_index].getInUse()) {
            free_index = (vct.size() + free_index - 1) % vct.size();
        }

        if (vct[free_index].getInUse()) { return -1; }

        while (checkIfInMaxDist(border_index, free_index)) {
            long long swap_index = (free_index + max_dist - 1) % vct.size();
            while (swap_index != free_index && checkMaxDistBoundsForSwapForRightToLeftShift(swap_index, free_index)) {
                swap_index = (vct.size() + swap_index - 1) % vct.size();
            }
            if (swap_index == free_index) {
                return -1;
            }
            activity_counter++;
            if (!is_virtual) {
                long long swap_original_index = vct[swap_index].getOriginalIndex();
                vct[free_index].setValue(vct[swap_index].getValue(), swap_original_index);
                vct[swap_original_index].setBitmap((vct.size() + swap_index - swap_original_index) % vct.size(), false);
                vct[swap_original_index].setBitmap((vct.size() + free_index - swap_original_index) % vct.size(), true);
                vct[swap_index].turnOff();
            }
            free_index = swap_index;
        }
        return is_virtual ? activity_counter : free_index;
    }

    void private_insert(const T& val, std::vector<Bucket>* for_resize) {
        const auto index = hashFunction(val);
        bool noCopy = true;
        bool placeWasFound = false;
        long long insert_index = index;
        long long corrected_index;
        long long upper_bound = max_dist + index;
        start_inside = std::chrono::system_clock::now();
        for (long long i = index; i < upper_bound; ++i) {
            corrected_index = i & vct.size()-1;
            if (!vct[corrected_index].getInUse() && !placeWasFound) {
                insert_index = corrected_index;
                placeWasFound = true;
            }
            else if (vct[corrected_index].getInUse() && vct[corrected_index].getValue() == val) {
                noCopy = false;
                break;
            }
        }
        end_inside = std::chrono::system_clock::now();
        elapsed_seconds_inside += end_inside-start_inside;

        if (!noCopy) {
//            end_inside = std::chrono::system_clock::now();
//            elapsed_seconds_inside += end_inside-start_inside;
            return;
        } else if (placeWasFound) {
            vct[insert_index].setValue(val, index);
            vct[index].setBitmap((insert_index - index + vct.size()) % vct.size(), true);
//            end_inside = std::chrono::system_clock::now();
//            elapsed_seconds_inside += end_inside-start_inside;
            return;
        }

        if (vct[index].bitmapIsFull()) {
            RESIZE++;
            if (&vct != for_resize) {
                HOP_INCREMENTED++;
                max_dist += 2;
                for (auto& buck : vct) {
                    buck.resize_max_dist(2);
                }
            } else {
                for_resize->emplace_back(max_dist);
                for_resize->back().setValue(val, 0);
            }
            resize(for_resize);
//            end_inside = std::chrono::system_clock::now();
//            elapsed_seconds_inside += end_inside-start_inside;
            return;
        }
        long long left_to_right = leftToRightShift((index + max_dist) % vct.size(), true);
        long long right_to_left = rightToLeftShift((index + max_dist) % vct.size(), true);
        if (left_to_right != -1 || right_to_left != -1) {
            if (right_to_left != -1 && (right_to_left <= left_to_right || left_to_right == -1)) {
                insert_index = rightToLeftShift((index + max_dist) % vct.size(), false);
                if (left_to_right == -1) {
                    ONLY_RIGHT_TO_LEFT++;
                } else {
                    RIGHT_TO_LEFT_IS_BETTER++;
                }
            } else if (left_to_right < right_to_left || right_to_left == -1) {
                insert_index = leftToRightShift((index + max_dist) % vct.size(), false);
                if (right_to_left == -1) {
                    ONLY_LEFT_TO_RIGHT++;
                } else {
                    LEFT_TO_RIGHT_IS_BETTER++;
                }
            }
            vct[insert_index].setValue(val, index);
            vct[index].setBitmap((insert_index - index + vct.size()) % vct.size(), true);
//            end_inside = std::chrono::system_clock::now();
//            elapsed_seconds_inside += end_inside-start_inside;
        } else {
            RESIZE++;
            if (&vct == for_resize) {
                for_resize->emplace_back(max_dist);
                for_resize->back().setValue(val, 0);
            } else {
                max_dist += 2;
                HOP_INCREMENTED++;
                for (auto& buck : vct) {
                    buck.resize_max_dist(2);
                }
            }
//            end_inside = std::chrono::system_clock::now();
//            elapsed_seconds_inside += end_inside-start_inside;
            resize(for_resize);
        }
    }

public:
    HopScotch(long long size, long long max_dist) : max_dist(max_dist > 0 && max_dist < size ? max_dist : 1) {
        vct.reserve(size > 0 ? size + 1 : max_dist + 2);
        vct.resize(size > 0 ? size : max_dist + 1, Bucket(max_dist));
    }

    void insert(T val) {
        private_insert(val, &vct);
    }

    friend std::ostream& operator<<(std::ostream& os, const HopScotch<T>& HT) {
        long long i = 0;
        for (const Bucket& buck : HT.vct) {
            os << '[' << i << ']' << ' ';
            if (buck.getInUse()) {
                os << buck.getValue() << '\t' << buck.getOriginalIndex() << '\t';
            } else {
                os << "empty" << '\t' << "Nn" << '\t';
            }
            for (long long ii = 0; ii < HT.max_dist; ii++) {
                os << buck.getBitmap(ii) << ' ';
            }
            os << '\n';
            i++;
        }
        os << '\n';
        return os;
    }

    void pop(T val) {
        long long index = hashFunction(val);
        for (long long i = index; i < max_dist + index; i++) {
            if (vct[i % vct.size()].getValue() == val && vct[i % vct.size()].getInUse()) {
                vct[i % vct.size()].turnOff();
                long long original_index = vct[i % vct.size()].getOriginalIndex();
                vct[original_index].setBitmap((i - original_index + vct.size()) % vct.size(), false);
                return;
            }
        }
    }

    long long get_quantity() const {
        long long quantity = 0;
        for (const auto& buck : vct) {
            if (buck.getInUse()) {
                quantity++;
            }
        }
        return quantity;
    }

    void get_shifts() const {
        std::cout << "ONLY_RIGHT_TO_LEFT" << '\t' << ONLY_RIGHT_TO_LEFT << "\n";
        std::cout << "ONLY_LEFT_TO_RIGHT" << '\t' << ONLY_LEFT_TO_RIGHT << "\n";
        std::cout << "RIGHT_TO_LEFT_IS_BETTER" << '\t' << RIGHT_TO_LEFT_IS_BETTER << "\n";
        std::cout << "LEFT_TO_RIGHT_IS_BETTER" << '\t' << LEFT_TO_RIGHT_IS_BETTER << "\n";
        std::cout << "RESIZE" << '\t' << RESIZE << "\n";
        std::cout << "AMOUNT_OF_TIMES_HOP_WAS_INCREMENTED" << '\t' << HOP_INCREMENTED << "\n";
    }
};

int main() {
    std::unordered_set<int> mp;
    HopScotch<int> my(128, 25);
    std::random_device dev;
    std::mt19937 rng(dev());
    std::uniform_int_distribution<int> rn(-2000000, 2000000);
    std::uniform_int_distribution<int> rn_for_pop(0, 100);
    std::chrono::time_point<std::chrono::system_clock> start = std::chrono::system_clock::now();
    std::chrono::time_point<std::chrono::system_clock> end = std::chrono::system_clock::now();
    std::chrono::duration<double> elapsed_seconds = end-start;
    std::chrono::duration<double> elapsed_seconds_set = end-start;
    int i = 0;
    while (i < 70000) {
        int var = rn(rng);
        if(!mp.contains(var)){
            start = std::chrono::system_clock::now();
            mp.insert(var);
            end = std::chrono::system_clock::now();
            elapsed_seconds_set += end - start;
            start = std::chrono::system_clock::now();
            my.insert(var);
            end = std::chrono::system_clock::now();
            elapsed_seconds += end - start;
            ++i;
        }
        if (rn_for_pop(rng) < 50) {
            start = std::chrono::system_clock::now();
            mp.erase(var);
            end = std::chrono::system_clock::now();
            elapsed_seconds_set += end - start;
            start = std::chrono::system_clock::now();
            my.pop(var);
            end = std::chrono::system_clock::now();
            elapsed_seconds += end - start;
            --i;
        }
    }
//    std::cout << my;
    my.get_shifts();
    std::cout << elapsed_seconds.count() << '\n';
    std::cout << elapsed_seconds_set.count() << '\n';
    std::cout << elapsed_seconds_inside.count() << '\n';
//    auto start = std::chrono::system_clock::now();
//    for(int i = 2; i <= 1048576; i*=2){
//        for(int j = i; j < i + 100000; ++j){
//            int v = j % i;
//        }
//    }
//    auto end = std::chrono::system_clock::now();
//    std::chrono::duration<double> elapsed_seconds = end-start;
//    std::cout << elapsed_seconds.count();
    return 0;
}
