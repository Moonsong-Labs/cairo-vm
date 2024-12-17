func main() {
    alloc_locals;

    local tmp = 3;
    let a = 17 - tmp;
    // Use custom hint to print the value of a
    %{ print(ids.a) %}
    return ();
}
