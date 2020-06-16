static void
set_row (matrix_t *dm, int row)
{
    for (int i = 0; i < dm_ncols (dm); i++) {
        dm_set (dm, row, i);
    }
}

static matrix_t *
enlarge_matrix (matrix_t *dm, int add_rows, int add_cols)
{
    matrix_t *new = RTmalloc (sizeof(matrix_t));
    dm_create (new, dm_nrows(dm) + add_rows, dm_ncols(dm) + add_cols);
    for (int i = 0; i < dm_nrows (dm); i++) {
        for (int j = 0; j < dm_ncols(dm); j++) {
            if (dm_is_set(dm, i, j)) {
                dm_set (new, i, j);
            }
        }
    }
    return new;
}

void
leap_add_leap_group (model_t por_model, model_t pre_por)
{
    matrix_t *dm = enlarge_matrix (GBgetDMInfo(pre_por), 1, 0);
    set_row (dm, dm_nrows (dm) - 1);
    GBsetDMInfo (por_model, dm);

    dm = enlarge_matrix (GBgetDMInfoMayWrite(pre_por), 1, 0);
    set_row (dm, dm_nrows (dm) - 1);
    GBsetDMInfoMayWrite (por_model, dm);

    dm = enlarge_matrix (GBgetDMInfoMustWrite(pre_por), 1, 0);
    set_row (dm, dm_nrows (dm) - 1);
    GBsetDMInfoMustWrite (por_model, dm);

    dm = enlarge_matrix (GBgetDMInfoRead(pre_por), 1, 0);
    set_row (dm, dm_nrows (dm) - 1);
    GBsetDMInfoRead (por_model, dm);
}
