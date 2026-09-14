class C {
  active : Boolean [0..1] unordered unique;
  scores : Integer [0..2] ordered nonunique;
}
object o : C {
  observe C::active = [false];
  observe C::scores = [0, 0];
}
