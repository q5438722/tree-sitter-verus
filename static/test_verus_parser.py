
def test_case_spec_compatible():
    with open('/home/v-tianychen/scripts/src_cmp.rs', 'r') as f:
        src_prog = f.read()
    with open('/home/v-tianychen/scripts/dst_cmp.rs', 'r') as f:
        dst_prog = f.read()
    print(spec_compatible(src_prog, dst_prog))
