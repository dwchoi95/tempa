def t(e):
    try:
        raise e
    except (KeyError, IndexError) as x:
        return "lookup " + type(x).__name__
    except ValueError:
        return "value"
    except:
        return "other"
    else:
        return "none"
print(t(KeyError), t(IndexError("i")), t(ValueError()), t(TypeError))
try:
    pass
except Exception:
    print("no")
else:
    print("else")
try:
    try:
        1 / 0
    except ZeroDivisionError:
        raise ValueError("v")
except ValueError as e:
    print(type(e.__context__).__name__)
try:
    raise KeyError("k") from IndexError()
except KeyError as e:
    print(repr(e), type(e.__cause__).__name__)
class MyErr(Exception):
    pass
try:
    raise MyErr("m")
except Exception as e:
    print(type(e).__name__, e.args, str(e))
try:
    assert 1 == 2, "msg"
except AssertionError as e:
    print("assert", e)
try:
    [][1]
except IndexError:
    print("index")
try:
    {}["x"]
except KeyError as e:
    print("key", e)
def h():
    try:
        return 1
    except Exception as e:
        pass
print(h())
try:
    int("x")
except ValueError:
    print("int")
