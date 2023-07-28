from itertools import combinations
import json
import os


def powerset(iterable):
    """powerset([1,2,3]) --> () (1,) (2,) (3,) (1,2) (1,3) (2,3) (1,2,3)"""
    subsets = []
    [subsets.extend(list(combinations(iterable, n))) for n in range(len(iterable) + 1)]
    return subsets


def add_lists(lst1, lst2):
    n = max(len(lst1), len(lst2))
    result = [
        lst1[i] + lst2[i] if i < len(lst1) and i < len(lst2) else lst1[i] if i < len(lst1) else lst2[i] if i < len(
            lst2) else 0 for i in range(n)]
    return result


def sub_lists(lst1, lst2):
    n = max(len(lst1), len(lst2))
    result = [
        lst1[i] - lst2[i] if i < len(lst1) and i < len(lst2) else lst1[i] if i < len(lst1) else lst2[i] if i < len(
            lst2) else 0 for i in range(n)]
    return result


def mul_lists(lst1, lst2):
    n = max(len(lst1), len(lst2))
    result = [
        lst1[i] * lst2[i] if i < len(lst1) and i < len(lst2) else lst1[i] if i < len(lst1) else lst2[i] if i < len(
            lst2) else 0 for i in range(n)]
    return result


def convolve(x, h):
    # determine the length of the input and filter
    n = len(x)
    m = len(h)

    # initialize the output
    y = [0] * (n + m - 1)

    # perform convolution
    for i, xi in enumerate(x):
        for j, hj in enumerate(h):
            y[i + j] += xi * hj

    return y


def file_to_json(file_name):
    f = open(f'{file_name}')
    try:
        data = json.load(f)

    except json.JSONDecodeError:
        return -1

    return data


def iterate_over_dir(func, directory='AcademicPowerIndicesOutput', params=None, skip_list=None):
    dtree_data_list = []

    for filename in os.listdir(directory):
        f = os.path.join(directory, filename)
        if os.path.isfile(f):
            print(filename)
            if skip_list is None or filename not in skip_list:
                f = file_to_json(f)
                if f != -1:
                    data = func(f, *params) if params is not None else func(f)
                    if data is not None:
                        dtree_data_list.extend(data)
    return dtree_data_list


def read_log(log_name):
    results = {}
    log_name = os.path.join('logs', log_name)

    with open(log_name, 'r') as f:
        for line in f:
            j = line.index(")")
            run = line[27:j]
            arr = run.split(', ')
            run = tuple([a[1:-1] for a in arr])
            res = line[j+4:-1]
            res = res.replace("\'", "\"")
            res = res.replace(")", "]")
            res = res.replace("(", "[")
            try:
                res = json.loads(res)
                results[run] = res
            except json.JSONDecodeError:
                print(f"could not decode line {line}")
                continue

    return results
